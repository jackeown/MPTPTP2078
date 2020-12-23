%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:56 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 457 expanded)
%              Number of clauses        :  103 ( 135 expanded)
%              Number of leaves         :   19 ( 171 expanded)
%              Depth                    :   25
%              Number of atoms          :  699 (5139 expanded)
%              Number of equality atoms :  215 ( 592 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,conjecture,(
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
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ( r1_tarski(X5,u1_struct_0(X2))
                             => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                             => ( r1_tarski(X5,u1_struct_0(X2))
                               => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & r1_tarski(X5,u1_struct_0(X2))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
     => ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5)
        & r1_tarski(sK5,u1_struct_0(X2))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
              & r1_tarski(X5,u1_struct_0(X2))
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5)
            & r1_tarski(X5,u1_struct_0(X2))
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                  & r1_tarski(X5,u1_struct_0(X2))
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5)
                & r1_tarski(X5,u1_struct_0(X2))
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                      & r1_tarski(X5,u1_struct_0(X2))
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5)
                    & r1_tarski(X5,u1_struct_0(sK2))
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5)
                        & r1_tarski(X5,u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & r1_tarski(X5,u1_struct_0(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
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
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    & r1_tarski(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f34,f41,f40,f39,f38,f37,f36])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_610,plain,
    ( r1_tarski(k7_relat_1(X0_54,X1_54),X0_54)
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1086,plain,
    ( r1_tarski(k7_relat_1(X0_54,X1_54),X0_54) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_601,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1094,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_606,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54)))
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1090,plain,
    ( r1_tarski(X0_54,X1_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_2307,plain,
    ( r1_tarski(X0_54,sK4) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1090])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_320,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_8,c_2])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_330,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_320,c_7])).

cnf(c_590,plain,
    ( r1_tarski(k2_relat_1(X0_54),X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X1_54))) ),
    inference(subtyping,[status(esa)],[c_330])).

cnf(c_1105,plain,
    ( r1_tarski(k2_relat_1(X0_54),X1_54) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_2526,plain,
    ( r1_tarski(X0_54,sK4) != iProver_top
    | r1_tarski(k2_relat_1(X0_54),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2307,c_1105])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_611,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X1_54)),X1_54)
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1085,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X1_54)),X1_54) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_607,plain,
    ( ~ r1_tarski(k1_relat_1(X0_54),X1_54)
    | ~ r1_tarski(k2_relat_1(X0_54),X2_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1089,plain,
    ( r1_tarski(k1_relat_1(X0_54),X1_54) != iProver_top
    | r1_tarski(k2_relat_1(X0_54),X2_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | k7_relset_1(X1_54,X2_54,X0_54,X3_54) = k9_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1088,plain,
    ( k7_relset_1(X0_54,X1_54,X2_54,X3_54) = k9_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_2361,plain,
    ( k7_relset_1(X0_54,X1_54,X2_54,X3_54) = k9_relat_1(X2_54,X3_54)
    | r1_tarski(k1_relat_1(X2_54),X0_54) != iProver_top
    | r1_tarski(k2_relat_1(X2_54),X1_54) != iProver_top
    | v1_relat_1(X2_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1089,c_1088])).

cnf(c_4103,plain,
    ( k7_relset_1(X0_54,X1_54,k7_relat_1(X2_54,X0_54),X3_54) = k9_relat_1(k7_relat_1(X2_54,X0_54),X3_54)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_54,X0_54)),X1_54) != iProver_top
    | v1_relat_1(X2_54) != iProver_top
    | v1_relat_1(k7_relat_1(X2_54,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_2361])).

cnf(c_13342,plain,
    ( k7_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(X1_54,X0_54),X2_54) = k9_relat_1(k7_relat_1(X1_54,X0_54),X2_54)
    | r1_tarski(k7_relat_1(X1_54,X0_54),sK4) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(k7_relat_1(X1_54,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2526,c_4103])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1087,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_2528,plain,
    ( r1_tarski(X0_54,sK4) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_2307,c_1087])).

cnf(c_15454,plain,
    ( k7_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(X1_54,X0_54),X2_54) = k9_relat_1(k7_relat_1(X1_54,X0_54),X2_54)
    | r1_tarski(k7_relat_1(X1_54,X0_54),sK4) != iProver_top
    | v1_relat_1(X1_54) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13342,c_2528])).

cnf(c_15458,plain,
    ( k7_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK4,X0_54),X1_54) = k9_relat_1(k7_relat_1(sK4,X0_54),X1_54)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_15454])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1287,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_1288,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1287])).

cnf(c_16242,plain,
    ( k7_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK4,X0_54),X1_54) = k9_relat_1(k7_relat_1(sK4,X0_54),X1_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15458,c_43,c_1288])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_598,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1097,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_598])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_340,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X4) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_341,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_345,plain,
    ( ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_20])).

cnf(c_346,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_345])).

cnf(c_589,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X0_56,X2_56)
    | ~ m1_pre_topc(X1_56,X2_56)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X3_56))))
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | ~ v2_pre_topc(X2_56)
    | ~ v2_pre_topc(X3_56)
    | ~ l1_pre_topc(X2_56)
    | ~ l1_pre_topc(X3_56)
    | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(X3_56),sK4,u1_struct_0(X0_56)) = k3_tmap_1(X2_56,X3_56,X1_56,X0_56,sK4)
    | u1_struct_0(X3_56) != u1_struct_0(sK1)
    | u1_struct_0(X1_56) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_1106,plain,
    ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),sK4,u1_struct_0(X2_56)) = k3_tmap_1(X3_56,X1_56,X0_56,X2_56,sK4)
    | u1_struct_0(X1_56) != u1_struct_0(sK1)
    | u1_struct_0(X0_56) != u1_struct_0(sK3)
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X3_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_1805,plain,
    ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK4,u1_struct_0(X1_56)) = k3_tmap_1(X2_56,sK1,X0_56,X1_56,sK4)
    | u1_struct_0(X0_56) != u1_struct_0(sK3)
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1106])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_34,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_35,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_36,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2031,plain,
    ( l1_pre_topc(X2_56) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | u1_struct_0(X0_56) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK4,u1_struct_0(X1_56)) = k3_tmap_1(X2_56,sK1,X0_56,X1_56,sK4)
    | v2_pre_topc(X2_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1805,c_34,c_35,c_36])).

cnf(c_2032,plain,
    ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK4,u1_struct_0(X1_56)) = k3_tmap_1(X2_56,sK1,X0_56,X1_56,sK4)
    | u1_struct_0(X0_56) != u1_struct_0(sK3)
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_2031])).

cnf(c_2044,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_56)) = k3_tmap_1(X1_56,sK1,sK3,X0_56,sK4)
    | m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X0_56,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_56) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2032])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_393,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_588,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_1107,plain,
    ( k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_1709,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_1094,c_1107])).

cnf(c_2045,plain,
    ( k3_tmap_1(X0_56,sK1,sK3,X1_56,sK4) = k7_relat_1(sK4,u1_struct_0(X1_56))
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_56) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2044,c_1709])).

cnf(c_2050,plain,
    ( m1_pre_topc(sK3,X0_56) != iProver_top
    | m1_pre_topc(X1_56,sK3) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | k3_tmap_1(X0_56,sK1,sK3,X1_56,sK4) = k7_relat_1(sK4,u1_struct_0(X1_56))
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2045,c_43])).

cnf(c_2051,plain,
    ( k3_tmap_1(X0_56,sK1,sK3,X1_56,sK4) = k7_relat_1(sK4,u1_struct_0(X1_56))
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_2050])).

cnf(c_2065,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1097,c_2051])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_31,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_32,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_33,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_40,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_44,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2216,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2065,c_31,c_32,c_33,c_40,c_44])).

cnf(c_1918,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k9_relat_1(sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_1094,c_1088])).

cnf(c_14,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_605,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1978,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_1918,c_605])).

cnf(c_2219,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_2216,c_1978])).

cnf(c_16246,plain,
    ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_16242,c_2219])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1082,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_1557,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1082])).

cnf(c_1630,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1557,c_43,c_1288])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_604,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1091,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_612,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ v1_relat_1(X2_54)
    | k9_relat_1(k7_relat_1(X2_54,X1_54),X0_54) = k9_relat_1(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1084,plain,
    ( k9_relat_1(k7_relat_1(X0_54,X1_54),X2_54) = k9_relat_1(X0_54,X2_54)
    | r1_tarski(X2_54,X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_2275,plain,
    ( k9_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_54,sK5)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_1084])).

cnf(c_2455,plain,
    ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k9_relat_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1630,c_2275])).

cnf(c_16247,plain,
    ( k9_relat_1(sK4,sK5) != k9_relat_1(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_16246,c_2455])).

cnf(c_16248,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_16247])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:16:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.25/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/1.48  
% 7.25/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.25/1.48  
% 7.25/1.48  ------  iProver source info
% 7.25/1.48  
% 7.25/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.25/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.25/1.48  git: non_committed_changes: false
% 7.25/1.48  git: last_make_outside_of_git: false
% 7.25/1.48  
% 7.25/1.48  ------ 
% 7.25/1.48  
% 7.25/1.48  ------ Input Options
% 7.25/1.48  
% 7.25/1.48  --out_options                           all
% 7.25/1.48  --tptp_safe_out                         true
% 7.25/1.48  --problem_path                          ""
% 7.25/1.48  --include_path                          ""
% 7.25/1.48  --clausifier                            res/vclausify_rel
% 7.25/1.48  --clausifier_options                    --mode clausify
% 7.25/1.48  --stdin                                 false
% 7.25/1.48  --stats_out                             all
% 7.25/1.48  
% 7.25/1.48  ------ General Options
% 7.25/1.48  
% 7.25/1.48  --fof                                   false
% 7.25/1.48  --time_out_real                         305.
% 7.25/1.48  --time_out_virtual                      -1.
% 7.25/1.48  --symbol_type_check                     false
% 7.25/1.48  --clausify_out                          false
% 7.25/1.48  --sig_cnt_out                           false
% 7.25/1.48  --trig_cnt_out                          false
% 7.25/1.48  --trig_cnt_out_tolerance                1.
% 7.25/1.48  --trig_cnt_out_sk_spl                   false
% 7.25/1.48  --abstr_cl_out                          false
% 7.25/1.48  
% 7.25/1.48  ------ Global Options
% 7.25/1.48  
% 7.25/1.48  --schedule                              default
% 7.25/1.48  --add_important_lit                     false
% 7.25/1.48  --prop_solver_per_cl                    1000
% 7.25/1.48  --min_unsat_core                        false
% 7.25/1.48  --soft_assumptions                      false
% 7.25/1.48  --soft_lemma_size                       3
% 7.25/1.48  --prop_impl_unit_size                   0
% 7.25/1.48  --prop_impl_unit                        []
% 7.25/1.48  --share_sel_clauses                     true
% 7.25/1.48  --reset_solvers                         false
% 7.25/1.48  --bc_imp_inh                            [conj_cone]
% 7.25/1.48  --conj_cone_tolerance                   3.
% 7.25/1.48  --extra_neg_conj                        none
% 7.25/1.48  --large_theory_mode                     true
% 7.25/1.48  --prolific_symb_bound                   200
% 7.25/1.48  --lt_threshold                          2000
% 7.25/1.48  --clause_weak_htbl                      true
% 7.25/1.48  --gc_record_bc_elim                     false
% 7.25/1.48  
% 7.25/1.48  ------ Preprocessing Options
% 7.25/1.48  
% 7.25/1.48  --preprocessing_flag                    true
% 7.25/1.48  --time_out_prep_mult                    0.1
% 7.25/1.48  --splitting_mode                        input
% 7.25/1.48  --splitting_grd                         true
% 7.25/1.48  --splitting_cvd                         false
% 7.25/1.48  --splitting_cvd_svl                     false
% 7.25/1.48  --splitting_nvd                         32
% 7.25/1.48  --sub_typing                            true
% 7.25/1.48  --prep_gs_sim                           true
% 7.25/1.48  --prep_unflatten                        true
% 7.25/1.48  --prep_res_sim                          true
% 7.25/1.48  --prep_upred                            true
% 7.25/1.48  --prep_sem_filter                       exhaustive
% 7.25/1.48  --prep_sem_filter_out                   false
% 7.25/1.48  --pred_elim                             true
% 7.25/1.48  --res_sim_input                         true
% 7.25/1.48  --eq_ax_congr_red                       true
% 7.25/1.48  --pure_diseq_elim                       true
% 7.25/1.48  --brand_transform                       false
% 7.25/1.48  --non_eq_to_eq                          false
% 7.25/1.48  --prep_def_merge                        true
% 7.25/1.48  --prep_def_merge_prop_impl              false
% 7.25/1.48  --prep_def_merge_mbd                    true
% 7.25/1.48  --prep_def_merge_tr_red                 false
% 7.25/1.48  --prep_def_merge_tr_cl                  false
% 7.25/1.48  --smt_preprocessing                     true
% 7.25/1.48  --smt_ac_axioms                         fast
% 7.25/1.48  --preprocessed_out                      false
% 7.25/1.48  --preprocessed_stats                    false
% 7.25/1.48  
% 7.25/1.48  ------ Abstraction refinement Options
% 7.25/1.48  
% 7.25/1.48  --abstr_ref                             []
% 7.25/1.48  --abstr_ref_prep                        false
% 7.25/1.48  --abstr_ref_until_sat                   false
% 7.25/1.48  --abstr_ref_sig_restrict                funpre
% 7.25/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.25/1.48  --abstr_ref_under                       []
% 7.25/1.48  
% 7.25/1.48  ------ SAT Options
% 7.25/1.48  
% 7.25/1.48  --sat_mode                              false
% 7.25/1.48  --sat_fm_restart_options                ""
% 7.25/1.48  --sat_gr_def                            false
% 7.25/1.48  --sat_epr_types                         true
% 7.25/1.48  --sat_non_cyclic_types                  false
% 7.25/1.48  --sat_finite_models                     false
% 7.25/1.48  --sat_fm_lemmas                         false
% 7.25/1.48  --sat_fm_prep                           false
% 7.25/1.48  --sat_fm_uc_incr                        true
% 7.25/1.48  --sat_out_model                         small
% 7.25/1.48  --sat_out_clauses                       false
% 7.25/1.48  
% 7.25/1.48  ------ QBF Options
% 7.25/1.48  
% 7.25/1.48  --qbf_mode                              false
% 7.25/1.48  --qbf_elim_univ                         false
% 7.25/1.48  --qbf_dom_inst                          none
% 7.25/1.48  --qbf_dom_pre_inst                      false
% 7.25/1.48  --qbf_sk_in                             false
% 7.25/1.48  --qbf_pred_elim                         true
% 7.25/1.48  --qbf_split                             512
% 7.25/1.48  
% 7.25/1.48  ------ BMC1 Options
% 7.25/1.48  
% 7.25/1.48  --bmc1_incremental                      false
% 7.25/1.48  --bmc1_axioms                           reachable_all
% 7.25/1.48  --bmc1_min_bound                        0
% 7.25/1.48  --bmc1_max_bound                        -1
% 7.25/1.48  --bmc1_max_bound_default                -1
% 7.25/1.48  --bmc1_symbol_reachability              true
% 7.25/1.48  --bmc1_property_lemmas                  false
% 7.25/1.48  --bmc1_k_induction                      false
% 7.25/1.48  --bmc1_non_equiv_states                 false
% 7.25/1.48  --bmc1_deadlock                         false
% 7.25/1.48  --bmc1_ucm                              false
% 7.25/1.48  --bmc1_add_unsat_core                   none
% 7.25/1.48  --bmc1_unsat_core_children              false
% 7.25/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.25/1.48  --bmc1_out_stat                         full
% 7.25/1.48  --bmc1_ground_init                      false
% 7.25/1.48  --bmc1_pre_inst_next_state              false
% 7.25/1.48  --bmc1_pre_inst_state                   false
% 7.25/1.48  --bmc1_pre_inst_reach_state             false
% 7.25/1.48  --bmc1_out_unsat_core                   false
% 7.25/1.48  --bmc1_aig_witness_out                  false
% 7.25/1.48  --bmc1_verbose                          false
% 7.25/1.48  --bmc1_dump_clauses_tptp                false
% 7.25/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.25/1.48  --bmc1_dump_file                        -
% 7.25/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.25/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.25/1.48  --bmc1_ucm_extend_mode                  1
% 7.25/1.48  --bmc1_ucm_init_mode                    2
% 7.25/1.48  --bmc1_ucm_cone_mode                    none
% 7.25/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.25/1.48  --bmc1_ucm_relax_model                  4
% 7.25/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.25/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.25/1.48  --bmc1_ucm_layered_model                none
% 7.25/1.48  --bmc1_ucm_max_lemma_size               10
% 7.25/1.48  
% 7.25/1.48  ------ AIG Options
% 7.25/1.48  
% 7.25/1.48  --aig_mode                              false
% 7.25/1.48  
% 7.25/1.48  ------ Instantiation Options
% 7.25/1.48  
% 7.25/1.48  --instantiation_flag                    true
% 7.25/1.48  --inst_sos_flag                         false
% 7.25/1.48  --inst_sos_phase                        true
% 7.25/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.25/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.25/1.48  --inst_lit_sel_side                     num_symb
% 7.25/1.48  --inst_solver_per_active                1400
% 7.25/1.48  --inst_solver_calls_frac                1.
% 7.25/1.48  --inst_passive_queue_type               priority_queues
% 7.25/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.25/1.48  --inst_passive_queues_freq              [25;2]
% 7.25/1.48  --inst_dismatching                      true
% 7.25/1.48  --inst_eager_unprocessed_to_passive     true
% 7.25/1.48  --inst_prop_sim_given                   true
% 7.25/1.48  --inst_prop_sim_new                     false
% 7.25/1.48  --inst_subs_new                         false
% 7.25/1.48  --inst_eq_res_simp                      false
% 7.25/1.48  --inst_subs_given                       false
% 7.25/1.48  --inst_orphan_elimination               true
% 7.25/1.48  --inst_learning_loop_flag               true
% 7.25/1.48  --inst_learning_start                   3000
% 7.25/1.48  --inst_learning_factor                  2
% 7.25/1.48  --inst_start_prop_sim_after_learn       3
% 7.25/1.48  --inst_sel_renew                        solver
% 7.25/1.48  --inst_lit_activity_flag                true
% 7.25/1.48  --inst_restr_to_given                   false
% 7.25/1.48  --inst_activity_threshold               500
% 7.25/1.48  --inst_out_proof                        true
% 7.25/1.48  
% 7.25/1.48  ------ Resolution Options
% 7.25/1.48  
% 7.25/1.48  --resolution_flag                       true
% 7.25/1.48  --res_lit_sel                           adaptive
% 7.25/1.48  --res_lit_sel_side                      none
% 7.25/1.48  --res_ordering                          kbo
% 7.25/1.48  --res_to_prop_solver                    active
% 7.25/1.48  --res_prop_simpl_new                    false
% 7.25/1.48  --res_prop_simpl_given                  true
% 7.25/1.48  --res_passive_queue_type                priority_queues
% 7.25/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.25/1.48  --res_passive_queues_freq               [15;5]
% 7.25/1.48  --res_forward_subs                      full
% 7.25/1.48  --res_backward_subs                     full
% 7.25/1.48  --res_forward_subs_resolution           true
% 7.25/1.48  --res_backward_subs_resolution          true
% 7.25/1.48  --res_orphan_elimination                true
% 7.25/1.48  --res_time_limit                        2.
% 7.25/1.48  --res_out_proof                         true
% 7.25/1.48  
% 7.25/1.48  ------ Superposition Options
% 7.25/1.48  
% 7.25/1.48  --superposition_flag                    true
% 7.25/1.48  --sup_passive_queue_type                priority_queues
% 7.25/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.25/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.25/1.48  --demod_completeness_check              fast
% 7.25/1.48  --demod_use_ground                      true
% 7.25/1.48  --sup_to_prop_solver                    passive
% 7.25/1.48  --sup_prop_simpl_new                    true
% 7.25/1.48  --sup_prop_simpl_given                  true
% 7.25/1.48  --sup_fun_splitting                     false
% 7.25/1.48  --sup_smt_interval                      50000
% 7.25/1.48  
% 7.25/1.48  ------ Superposition Simplification Setup
% 7.25/1.48  
% 7.25/1.48  --sup_indices_passive                   []
% 7.25/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.25/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.48  --sup_full_bw                           [BwDemod]
% 7.25/1.48  --sup_immed_triv                        [TrivRules]
% 7.25/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.48  --sup_immed_bw_main                     []
% 7.25/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.25/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.48  
% 7.25/1.48  ------ Combination Options
% 7.25/1.48  
% 7.25/1.48  --comb_res_mult                         3
% 7.25/1.48  --comb_sup_mult                         2
% 7.25/1.48  --comb_inst_mult                        10
% 7.25/1.48  
% 7.25/1.48  ------ Debug Options
% 7.25/1.48  
% 7.25/1.48  --dbg_backtrace                         false
% 7.25/1.48  --dbg_dump_prop_clauses                 false
% 7.25/1.48  --dbg_dump_prop_clauses_file            -
% 7.25/1.48  --dbg_out_stat                          false
% 7.25/1.48  ------ Parsing...
% 7.25/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.25/1.48  
% 7.25/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.25/1.48  
% 7.25/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.25/1.48  
% 7.25/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.25/1.48  ------ Proving...
% 7.25/1.48  ------ Problem Properties 
% 7.25/1.48  
% 7.25/1.48  
% 7.25/1.48  clauses                                 27
% 7.25/1.48  conjectures                             15
% 7.25/1.48  EPR                                     11
% 7.25/1.48  Horn                                    26
% 7.25/1.48  unary                                   16
% 7.25/1.48  binary                                  6
% 7.25/1.48  lits                                    54
% 7.25/1.48  lits eq                                 7
% 7.25/1.48  fd_pure                                 0
% 7.25/1.48  fd_pseudo                               0
% 7.25/1.48  fd_cond                                 0
% 7.25/1.48  fd_pseudo_cond                          0
% 7.25/1.48  AC symbols                              0
% 7.25/1.48  
% 7.25/1.48  ------ Schedule dynamic 5 is on 
% 7.25/1.48  
% 7.25/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.25/1.48  
% 7.25/1.48  
% 7.25/1.48  ------ 
% 7.25/1.48  Current options:
% 7.25/1.48  ------ 
% 7.25/1.48  
% 7.25/1.48  ------ Input Options
% 7.25/1.48  
% 7.25/1.48  --out_options                           all
% 7.25/1.48  --tptp_safe_out                         true
% 7.25/1.48  --problem_path                          ""
% 7.25/1.48  --include_path                          ""
% 7.25/1.48  --clausifier                            res/vclausify_rel
% 7.25/1.48  --clausifier_options                    --mode clausify
% 7.25/1.48  --stdin                                 false
% 7.25/1.48  --stats_out                             all
% 7.25/1.48  
% 7.25/1.48  ------ General Options
% 7.25/1.48  
% 7.25/1.48  --fof                                   false
% 7.25/1.48  --time_out_real                         305.
% 7.25/1.48  --time_out_virtual                      -1.
% 7.25/1.48  --symbol_type_check                     false
% 7.25/1.48  --clausify_out                          false
% 7.25/1.48  --sig_cnt_out                           false
% 7.25/1.48  --trig_cnt_out                          false
% 7.25/1.48  --trig_cnt_out_tolerance                1.
% 7.25/1.48  --trig_cnt_out_sk_spl                   false
% 7.25/1.48  --abstr_cl_out                          false
% 7.25/1.48  
% 7.25/1.48  ------ Global Options
% 7.25/1.48  
% 7.25/1.48  --schedule                              default
% 7.25/1.48  --add_important_lit                     false
% 7.25/1.48  --prop_solver_per_cl                    1000
% 7.25/1.48  --min_unsat_core                        false
% 7.25/1.48  --soft_assumptions                      false
% 7.25/1.48  --soft_lemma_size                       3
% 7.25/1.48  --prop_impl_unit_size                   0
% 7.25/1.48  --prop_impl_unit                        []
% 7.25/1.48  --share_sel_clauses                     true
% 7.25/1.48  --reset_solvers                         false
% 7.25/1.48  --bc_imp_inh                            [conj_cone]
% 7.25/1.48  --conj_cone_tolerance                   3.
% 7.25/1.48  --extra_neg_conj                        none
% 7.25/1.48  --large_theory_mode                     true
% 7.25/1.48  --prolific_symb_bound                   200
% 7.25/1.48  --lt_threshold                          2000
% 7.25/1.48  --clause_weak_htbl                      true
% 7.25/1.48  --gc_record_bc_elim                     false
% 7.25/1.48  
% 7.25/1.48  ------ Preprocessing Options
% 7.25/1.48  
% 7.25/1.48  --preprocessing_flag                    true
% 7.25/1.48  --time_out_prep_mult                    0.1
% 7.25/1.48  --splitting_mode                        input
% 7.25/1.48  --splitting_grd                         true
% 7.25/1.48  --splitting_cvd                         false
% 7.25/1.48  --splitting_cvd_svl                     false
% 7.25/1.48  --splitting_nvd                         32
% 7.25/1.48  --sub_typing                            true
% 7.25/1.48  --prep_gs_sim                           true
% 7.25/1.48  --prep_unflatten                        true
% 7.25/1.48  --prep_res_sim                          true
% 7.25/1.48  --prep_upred                            true
% 7.25/1.48  --prep_sem_filter                       exhaustive
% 7.25/1.48  --prep_sem_filter_out                   false
% 7.25/1.48  --pred_elim                             true
% 7.25/1.48  --res_sim_input                         true
% 7.25/1.48  --eq_ax_congr_red                       true
% 7.25/1.48  --pure_diseq_elim                       true
% 7.25/1.48  --brand_transform                       false
% 7.25/1.48  --non_eq_to_eq                          false
% 7.25/1.48  --prep_def_merge                        true
% 7.25/1.48  --prep_def_merge_prop_impl              false
% 7.25/1.48  --prep_def_merge_mbd                    true
% 7.25/1.48  --prep_def_merge_tr_red                 false
% 7.25/1.48  --prep_def_merge_tr_cl                  false
% 7.25/1.48  --smt_preprocessing                     true
% 7.25/1.48  --smt_ac_axioms                         fast
% 7.25/1.48  --preprocessed_out                      false
% 7.25/1.48  --preprocessed_stats                    false
% 7.25/1.48  
% 7.25/1.48  ------ Abstraction refinement Options
% 7.25/1.48  
% 7.25/1.48  --abstr_ref                             []
% 7.25/1.48  --abstr_ref_prep                        false
% 7.25/1.48  --abstr_ref_until_sat                   false
% 7.25/1.48  --abstr_ref_sig_restrict                funpre
% 7.25/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.25/1.48  --abstr_ref_under                       []
% 7.25/1.48  
% 7.25/1.48  ------ SAT Options
% 7.25/1.48  
% 7.25/1.48  --sat_mode                              false
% 7.25/1.48  --sat_fm_restart_options                ""
% 7.25/1.48  --sat_gr_def                            false
% 7.25/1.48  --sat_epr_types                         true
% 7.25/1.48  --sat_non_cyclic_types                  false
% 7.25/1.48  --sat_finite_models                     false
% 7.25/1.48  --sat_fm_lemmas                         false
% 7.25/1.48  --sat_fm_prep                           false
% 7.25/1.48  --sat_fm_uc_incr                        true
% 7.25/1.48  --sat_out_model                         small
% 7.25/1.48  --sat_out_clauses                       false
% 7.25/1.48  
% 7.25/1.48  ------ QBF Options
% 7.25/1.48  
% 7.25/1.48  --qbf_mode                              false
% 7.25/1.48  --qbf_elim_univ                         false
% 7.25/1.48  --qbf_dom_inst                          none
% 7.25/1.48  --qbf_dom_pre_inst                      false
% 7.25/1.48  --qbf_sk_in                             false
% 7.25/1.48  --qbf_pred_elim                         true
% 7.25/1.48  --qbf_split                             512
% 7.25/1.48  
% 7.25/1.48  ------ BMC1 Options
% 7.25/1.48  
% 7.25/1.48  --bmc1_incremental                      false
% 7.25/1.48  --bmc1_axioms                           reachable_all
% 7.25/1.48  --bmc1_min_bound                        0
% 7.25/1.48  --bmc1_max_bound                        -1
% 7.25/1.48  --bmc1_max_bound_default                -1
% 7.25/1.48  --bmc1_symbol_reachability              true
% 7.25/1.48  --bmc1_property_lemmas                  false
% 7.25/1.48  --bmc1_k_induction                      false
% 7.25/1.48  --bmc1_non_equiv_states                 false
% 7.25/1.48  --bmc1_deadlock                         false
% 7.25/1.48  --bmc1_ucm                              false
% 7.25/1.48  --bmc1_add_unsat_core                   none
% 7.25/1.48  --bmc1_unsat_core_children              false
% 7.25/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.25/1.48  --bmc1_out_stat                         full
% 7.25/1.48  --bmc1_ground_init                      false
% 7.25/1.48  --bmc1_pre_inst_next_state              false
% 7.25/1.48  --bmc1_pre_inst_state                   false
% 7.25/1.48  --bmc1_pre_inst_reach_state             false
% 7.25/1.48  --bmc1_out_unsat_core                   false
% 7.25/1.48  --bmc1_aig_witness_out                  false
% 7.25/1.48  --bmc1_verbose                          false
% 7.25/1.48  --bmc1_dump_clauses_tptp                false
% 7.25/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.25/1.48  --bmc1_dump_file                        -
% 7.25/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.25/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.25/1.48  --bmc1_ucm_extend_mode                  1
% 7.25/1.48  --bmc1_ucm_init_mode                    2
% 7.25/1.48  --bmc1_ucm_cone_mode                    none
% 7.25/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.25/1.48  --bmc1_ucm_relax_model                  4
% 7.25/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.25/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.25/1.48  --bmc1_ucm_layered_model                none
% 7.25/1.48  --bmc1_ucm_max_lemma_size               10
% 7.25/1.48  
% 7.25/1.48  ------ AIG Options
% 7.25/1.48  
% 7.25/1.48  --aig_mode                              false
% 7.25/1.48  
% 7.25/1.48  ------ Instantiation Options
% 7.25/1.48  
% 7.25/1.48  --instantiation_flag                    true
% 7.25/1.48  --inst_sos_flag                         false
% 7.25/1.48  --inst_sos_phase                        true
% 7.25/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.25/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.25/1.48  --inst_lit_sel_side                     none
% 7.25/1.48  --inst_solver_per_active                1400
% 7.25/1.48  --inst_solver_calls_frac                1.
% 7.25/1.48  --inst_passive_queue_type               priority_queues
% 7.25/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.25/1.48  --inst_passive_queues_freq              [25;2]
% 7.25/1.48  --inst_dismatching                      true
% 7.25/1.48  --inst_eager_unprocessed_to_passive     true
% 7.25/1.48  --inst_prop_sim_given                   true
% 7.25/1.48  --inst_prop_sim_new                     false
% 7.25/1.48  --inst_subs_new                         false
% 7.25/1.48  --inst_eq_res_simp                      false
% 7.25/1.48  --inst_subs_given                       false
% 7.25/1.48  --inst_orphan_elimination               true
% 7.25/1.48  --inst_learning_loop_flag               true
% 7.25/1.48  --inst_learning_start                   3000
% 7.25/1.48  --inst_learning_factor                  2
% 7.25/1.48  --inst_start_prop_sim_after_learn       3
% 7.25/1.48  --inst_sel_renew                        solver
% 7.25/1.48  --inst_lit_activity_flag                true
% 7.25/1.48  --inst_restr_to_given                   false
% 7.25/1.48  --inst_activity_threshold               500
% 7.25/1.48  --inst_out_proof                        true
% 7.25/1.48  
% 7.25/1.48  ------ Resolution Options
% 7.25/1.48  
% 7.25/1.48  --resolution_flag                       false
% 7.25/1.48  --res_lit_sel                           adaptive
% 7.25/1.48  --res_lit_sel_side                      none
% 7.25/1.48  --res_ordering                          kbo
% 7.25/1.48  --res_to_prop_solver                    active
% 7.25/1.48  --res_prop_simpl_new                    false
% 7.25/1.48  --res_prop_simpl_given                  true
% 7.25/1.48  --res_passive_queue_type                priority_queues
% 7.25/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.25/1.48  --res_passive_queues_freq               [15;5]
% 7.25/1.48  --res_forward_subs                      full
% 7.25/1.48  --res_backward_subs                     full
% 7.25/1.48  --res_forward_subs_resolution           true
% 7.25/1.48  --res_backward_subs_resolution          true
% 7.25/1.48  --res_orphan_elimination                true
% 7.25/1.48  --res_time_limit                        2.
% 7.25/1.48  --res_out_proof                         true
% 7.25/1.48  
% 7.25/1.48  ------ Superposition Options
% 7.25/1.48  
% 7.25/1.48  --superposition_flag                    true
% 7.25/1.48  --sup_passive_queue_type                priority_queues
% 7.25/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.25/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.25/1.48  --demod_completeness_check              fast
% 7.25/1.48  --demod_use_ground                      true
% 7.25/1.48  --sup_to_prop_solver                    passive
% 7.25/1.48  --sup_prop_simpl_new                    true
% 7.25/1.48  --sup_prop_simpl_given                  true
% 7.25/1.48  --sup_fun_splitting                     false
% 7.25/1.48  --sup_smt_interval                      50000
% 7.25/1.48  
% 7.25/1.48  ------ Superposition Simplification Setup
% 7.25/1.48  
% 7.25/1.48  --sup_indices_passive                   []
% 7.25/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.25/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.48  --sup_full_bw                           [BwDemod]
% 7.25/1.48  --sup_immed_triv                        [TrivRules]
% 7.25/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.48  --sup_immed_bw_main                     []
% 7.25/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.25/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.48  
% 7.25/1.48  ------ Combination Options
% 7.25/1.48  
% 7.25/1.48  --comb_res_mult                         3
% 7.25/1.48  --comb_sup_mult                         2
% 7.25/1.48  --comb_inst_mult                        10
% 7.25/1.48  
% 7.25/1.48  ------ Debug Options
% 7.25/1.48  
% 7.25/1.48  --dbg_backtrace                         false
% 7.25/1.48  --dbg_dump_prop_clauses                 false
% 7.25/1.48  --dbg_dump_prop_clauses_file            -
% 7.25/1.48  --dbg_out_stat                          false
% 7.25/1.48  
% 7.25/1.48  
% 7.25/1.48  
% 7.25/1.48  
% 7.25/1.48  ------ Proving...
% 7.25/1.48  
% 7.25/1.48  
% 7.25/1.48  % SZS status Theorem for theBenchmark.p
% 7.25/1.48  
% 7.25/1.48   Resolution empty clause
% 7.25/1.48  
% 7.25/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.25/1.48  
% 7.25/1.48  fof(f6,axiom,(
% 7.25/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f21,plain,(
% 7.25/1.48    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 7.25/1.48    inference(ennf_transformation,[],[f6])).
% 7.25/1.48  
% 7.25/1.48  fof(f49,plain,(
% 7.25/1.48    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f21])).
% 7.25/1.48  
% 7.25/1.48  fof(f14,conjecture,(
% 7.25/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f15,negated_conjecture,(
% 7.25/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 7.25/1.48    inference(negated_conjecture,[],[f14])).
% 7.25/1.48  
% 7.25/1.48  fof(f33,plain,(
% 7.25/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.25/1.48    inference(ennf_transformation,[],[f15])).
% 7.25/1.48  
% 7.25/1.48  fof(f34,plain,(
% 7.25/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.25/1.48    inference(flattening,[],[f33])).
% 7.25/1.48  
% 7.25/1.48  fof(f41,plain,(
% 7.25/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5) & r1_tarski(sK5,u1_struct_0(X2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 7.25/1.48    introduced(choice_axiom,[])).
% 7.25/1.48  
% 7.25/1.48  fof(f40,plain,(
% 7.25/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.25/1.48    introduced(choice_axiom,[])).
% 7.25/1.48  
% 7.25/1.48  fof(f39,plain,(
% 7.25/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.25/1.48    introduced(choice_axiom,[])).
% 7.25/1.48  
% 7.25/1.48  fof(f38,plain,(
% 7.25/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.25/1.48    introduced(choice_axiom,[])).
% 7.25/1.48  
% 7.25/1.48  fof(f37,plain,(
% 7.25/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.25/1.48    introduced(choice_axiom,[])).
% 7.25/1.48  
% 7.25/1.48  fof(f36,plain,(
% 7.25/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.25/1.48    introduced(choice_axiom,[])).
% 7.25/1.48  
% 7.25/1.48  fof(f42,plain,(
% 7.25/1.48    (((((k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.25/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f34,f41,f40,f39,f38,f37,f36])).
% 7.25/1.48  
% 7.25/1.48  fof(f69,plain,(
% 7.25/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f11,axiom,(
% 7.25/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f27,plain,(
% 7.25/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.25/1.48    inference(ennf_transformation,[],[f11])).
% 7.25/1.48  
% 7.25/1.48  fof(f28,plain,(
% 7.25/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.25/1.48    inference(flattening,[],[f27])).
% 7.25/1.48  
% 7.25/1.48  fof(f54,plain,(
% 7.25/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 7.25/1.48    inference(cnf_transformation,[],[f28])).
% 7.25/1.48  
% 7.25/1.48  fof(f8,axiom,(
% 7.25/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f16,plain,(
% 7.25/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.25/1.48    inference(pure_predicate_removal,[],[f8])).
% 7.25/1.48  
% 7.25/1.48  fof(f23,plain,(
% 7.25/1.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.25/1.48    inference(ennf_transformation,[],[f16])).
% 7.25/1.48  
% 7.25/1.48  fof(f51,plain,(
% 7.25/1.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.25/1.48    inference(cnf_transformation,[],[f23])).
% 7.25/1.48  
% 7.25/1.48  fof(f2,axiom,(
% 7.25/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f18,plain,(
% 7.25/1.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.25/1.48    inference(ennf_transformation,[],[f2])).
% 7.25/1.48  
% 7.25/1.48  fof(f35,plain,(
% 7.25/1.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.25/1.48    inference(nnf_transformation,[],[f18])).
% 7.25/1.48  
% 7.25/1.48  fof(f44,plain,(
% 7.25/1.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f35])).
% 7.25/1.48  
% 7.25/1.48  fof(f7,axiom,(
% 7.25/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f22,plain,(
% 7.25/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.25/1.48    inference(ennf_transformation,[],[f7])).
% 7.25/1.48  
% 7.25/1.48  fof(f50,plain,(
% 7.25/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.25/1.48    inference(cnf_transformation,[],[f22])).
% 7.25/1.48  
% 7.25/1.48  fof(f5,axiom,(
% 7.25/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f20,plain,(
% 7.25/1.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.25/1.48    inference(ennf_transformation,[],[f5])).
% 7.25/1.48  
% 7.25/1.48  fof(f48,plain,(
% 7.25/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f20])).
% 7.25/1.48  
% 7.25/1.48  fof(f10,axiom,(
% 7.25/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f25,plain,(
% 7.25/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.25/1.48    inference(ennf_transformation,[],[f10])).
% 7.25/1.48  
% 7.25/1.48  fof(f26,plain,(
% 7.25/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.25/1.48    inference(flattening,[],[f25])).
% 7.25/1.48  
% 7.25/1.48  fof(f53,plain,(
% 7.25/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f26])).
% 7.25/1.48  
% 7.25/1.48  fof(f9,axiom,(
% 7.25/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f24,plain,(
% 7.25/1.48    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.25/1.48    inference(ennf_transformation,[],[f9])).
% 7.25/1.48  
% 7.25/1.48  fof(f52,plain,(
% 7.25/1.48    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.25/1.48    inference(cnf_transformation,[],[f24])).
% 7.25/1.48  
% 7.25/1.48  fof(f64,plain,(
% 7.25/1.48    m1_pre_topc(sK2,sK0)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f13,axiom,(
% 7.25/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f31,plain,(
% 7.25/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.25/1.48    inference(ennf_transformation,[],[f13])).
% 7.25/1.48  
% 7.25/1.48  fof(f32,plain,(
% 7.25/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.25/1.48    inference(flattening,[],[f31])).
% 7.25/1.48  
% 7.25/1.48  fof(f56,plain,(
% 7.25/1.48    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f32])).
% 7.25/1.48  
% 7.25/1.48  fof(f68,plain,(
% 7.25/1.48    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f67,plain,(
% 7.25/1.48    v1_funct_1(sK4)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f60,plain,(
% 7.25/1.48    ~v2_struct_0(sK1)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f61,plain,(
% 7.25/1.48    v2_pre_topc(sK1)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f62,plain,(
% 7.25/1.48    l1_pre_topc(sK1)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f12,axiom,(
% 7.25/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f29,plain,(
% 7.25/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.25/1.48    inference(ennf_transformation,[],[f12])).
% 7.25/1.48  
% 7.25/1.48  fof(f30,plain,(
% 7.25/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.25/1.48    inference(flattening,[],[f29])).
% 7.25/1.48  
% 7.25/1.48  fof(f55,plain,(
% 7.25/1.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f30])).
% 7.25/1.48  
% 7.25/1.48  fof(f57,plain,(
% 7.25/1.48    ~v2_struct_0(sK0)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f58,plain,(
% 7.25/1.48    v2_pre_topc(sK0)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f59,plain,(
% 7.25/1.48    l1_pre_topc(sK0)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f66,plain,(
% 7.25/1.48    m1_pre_topc(sK3,sK0)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f70,plain,(
% 7.25/1.48    m1_pre_topc(sK2,sK3)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f73,plain,(
% 7.25/1.48    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f1,axiom,(
% 7.25/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f17,plain,(
% 7.25/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.25/1.48    inference(ennf_transformation,[],[f1])).
% 7.25/1.48  
% 7.25/1.48  fof(f43,plain,(
% 7.25/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f17])).
% 7.25/1.48  
% 7.25/1.48  fof(f72,plain,(
% 7.25/1.48    r1_tarski(sK5,u1_struct_0(sK2))),
% 7.25/1.48    inference(cnf_transformation,[],[f42])).
% 7.25/1.48  
% 7.25/1.48  fof(f4,axiom,(
% 7.25/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f19,plain,(
% 7.25/1.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 7.25/1.48    inference(ennf_transformation,[],[f4])).
% 7.25/1.48  
% 7.25/1.48  fof(f47,plain,(
% 7.25/1.48    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f19])).
% 7.25/1.48  
% 7.25/1.48  cnf(c_6,plain,
% 7.25/1.48      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_610,plain,
% 7.25/1.48      ( r1_tarski(k7_relat_1(X0_54,X1_54),X0_54) | ~ v1_relat_1(X0_54) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1086,plain,
% 7.25/1.48      ( r1_tarski(k7_relat_1(X0_54,X1_54),X0_54) = iProver_top
% 7.25/1.48      | v1_relat_1(X0_54) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_18,negated_conjecture,
% 7.25/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.25/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_601,negated_conjecture,
% 7.25/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_18]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1094,plain,
% 7.25/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_11,plain,
% 7.25/1.48      ( ~ r1_tarski(X0,X1)
% 7.25/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.25/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
% 7.25/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_606,plain,
% 7.25/1.48      ( ~ r1_tarski(X0_54,X1_54)
% 7.25/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54)))
% 7.25/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_11]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1090,plain,
% 7.25/1.48      ( r1_tarski(X0_54,X1_54) != iProver_top
% 7.25/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.25/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2307,plain,
% 7.25/1.48      ( r1_tarski(X0_54,sK4) != iProver_top
% 7.25/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_1094,c_1090]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_8,plain,
% 7.25/1.48      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.25/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2,plain,
% 7.25/1.48      ( r1_tarski(k2_relat_1(X0),X1) | ~ v5_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_320,plain,
% 7.25/1.48      ( r1_tarski(k2_relat_1(X0),X1)
% 7.25/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.25/1.48      | ~ v1_relat_1(X0) ),
% 7.25/1.48      inference(resolution,[status(thm)],[c_8,c_2]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_7,plain,
% 7.25/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_330,plain,
% 7.25/1.48      ( r1_tarski(k2_relat_1(X0),X1)
% 7.25/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.25/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_320,c_7]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_590,plain,
% 7.25/1.48      ( r1_tarski(k2_relat_1(X0_54),X1_54)
% 7.25/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X1_54))) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_330]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1105,plain,
% 7.25/1.48      ( r1_tarski(k2_relat_1(X0_54),X1_54) = iProver_top
% 7.25/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X1_54))) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2526,plain,
% 7.25/1.48      ( r1_tarski(X0_54,sK4) != iProver_top
% 7.25/1.48      | r1_tarski(k2_relat_1(X0_54),u1_struct_0(sK1)) = iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_2307,c_1105]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_5,plain,
% 7.25/1.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_611,plain,
% 7.25/1.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X1_54)),X1_54)
% 7.25/1.48      | ~ v1_relat_1(X0_54) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1085,plain,
% 7.25/1.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X1_54)),X1_54) = iProver_top
% 7.25/1.48      | v1_relat_1(X0_54) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_10,plain,
% 7.25/1.48      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.25/1.48      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.25/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.48      | ~ v1_relat_1(X0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_607,plain,
% 7.25/1.48      ( ~ r1_tarski(k1_relat_1(X0_54),X1_54)
% 7.25/1.48      | ~ r1_tarski(k2_relat_1(X0_54),X2_54)
% 7.25/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.25/1.48      | ~ v1_relat_1(X0_54) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_10]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1089,plain,
% 7.25/1.48      ( r1_tarski(k1_relat_1(X0_54),X1_54) != iProver_top
% 7.25/1.48      | r1_tarski(k2_relat_1(X0_54),X2_54) != iProver_top
% 7.25/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) = iProver_top
% 7.25/1.48      | v1_relat_1(X0_54) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_9,plain,
% 7.25/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.48      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.25/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_608,plain,
% 7.25/1.48      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.25/1.48      | k7_relset_1(X1_54,X2_54,X0_54,X3_54) = k9_relat_1(X0_54,X3_54) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1088,plain,
% 7.25/1.48      ( k7_relset_1(X0_54,X1_54,X2_54,X3_54) = k9_relat_1(X2_54,X3_54)
% 7.25/1.48      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2361,plain,
% 7.25/1.48      ( k7_relset_1(X0_54,X1_54,X2_54,X3_54) = k9_relat_1(X2_54,X3_54)
% 7.25/1.48      | r1_tarski(k1_relat_1(X2_54),X0_54) != iProver_top
% 7.25/1.48      | r1_tarski(k2_relat_1(X2_54),X1_54) != iProver_top
% 7.25/1.48      | v1_relat_1(X2_54) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_1089,c_1088]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_4103,plain,
% 7.25/1.48      ( k7_relset_1(X0_54,X1_54,k7_relat_1(X2_54,X0_54),X3_54) = k9_relat_1(k7_relat_1(X2_54,X0_54),X3_54)
% 7.25/1.48      | r1_tarski(k2_relat_1(k7_relat_1(X2_54,X0_54)),X1_54) != iProver_top
% 7.25/1.48      | v1_relat_1(X2_54) != iProver_top
% 7.25/1.48      | v1_relat_1(k7_relat_1(X2_54,X0_54)) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_1085,c_2361]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_13342,plain,
% 7.25/1.48      ( k7_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(X1_54,X0_54),X2_54) = k9_relat_1(k7_relat_1(X1_54,X0_54),X2_54)
% 7.25/1.48      | r1_tarski(k7_relat_1(X1_54,X0_54),sK4) != iProver_top
% 7.25/1.48      | v1_relat_1(X1_54) != iProver_top
% 7.25/1.48      | v1_relat_1(k7_relat_1(X1_54,X0_54)) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_2526,c_4103]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_609,plain,
% 7.25/1.48      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.25/1.48      | v1_relat_1(X0_54) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1087,plain,
% 7.25/1.48      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.25/1.48      | v1_relat_1(X0_54) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2528,plain,
% 7.25/1.48      ( r1_tarski(X0_54,sK4) != iProver_top | v1_relat_1(X0_54) = iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_2307,c_1087]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_15454,plain,
% 7.25/1.48      ( k7_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(X1_54,X0_54),X2_54) = k9_relat_1(k7_relat_1(X1_54,X0_54),X2_54)
% 7.25/1.48      | r1_tarski(k7_relat_1(X1_54,X0_54),sK4) != iProver_top
% 7.25/1.48      | v1_relat_1(X1_54) != iProver_top ),
% 7.25/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_13342,c_2528]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_15458,plain,
% 7.25/1.48      ( k7_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK4,X0_54),X1_54) = k9_relat_1(k7_relat_1(sK4,X0_54),X1_54)
% 7.25/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_1086,c_15454]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_43,plain,
% 7.25/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1287,plain,
% 7.25/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.25/1.48      | v1_relat_1(sK4) ),
% 7.25/1.48      inference(instantiation,[status(thm)],[c_609]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1288,plain,
% 7.25/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.25/1.48      | v1_relat_1(sK4) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_1287]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_16242,plain,
% 7.25/1.48      ( k7_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK4,X0_54),X1_54) = k9_relat_1(k7_relat_1(sK4,X0_54),X1_54) ),
% 7.25/1.48      inference(global_propositional_subsumption,
% 7.25/1.48                [status(thm)],
% 7.25/1.48                [c_15458,c_43,c_1288]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_23,negated_conjecture,
% 7.25/1.48      ( m1_pre_topc(sK2,sK0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_598,negated_conjecture,
% 7.25/1.48      ( m1_pre_topc(sK2,sK0) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_23]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1097,plain,
% 7.25/1.48      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_598]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_13,plain,
% 7.25/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.25/1.48      | ~ m1_pre_topc(X3,X1)
% 7.25/1.48      | ~ m1_pre_topc(X3,X4)
% 7.25/1.48      | ~ m1_pre_topc(X1,X4)
% 7.25/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.25/1.48      | v2_struct_0(X4)
% 7.25/1.48      | v2_struct_0(X2)
% 7.25/1.48      | ~ v2_pre_topc(X2)
% 7.25/1.48      | ~ v2_pre_topc(X4)
% 7.25/1.48      | ~ l1_pre_topc(X2)
% 7.25/1.48      | ~ l1_pre_topc(X4)
% 7.25/1.48      | ~ v1_funct_1(X0)
% 7.25/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_19,negated_conjecture,
% 7.25/1.48      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 7.25/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_340,plain,
% 7.25/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.25/1.48      | ~ m1_pre_topc(X0,X2)
% 7.25/1.48      | ~ m1_pre_topc(X1,X2)
% 7.25/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.25/1.48      | v2_struct_0(X2)
% 7.25/1.48      | v2_struct_0(X4)
% 7.25/1.48      | ~ v2_pre_topc(X4)
% 7.25/1.48      | ~ v2_pre_topc(X2)
% 7.25/1.48      | ~ l1_pre_topc(X4)
% 7.25/1.48      | ~ l1_pre_topc(X2)
% 7.25/1.48      | ~ v1_funct_1(X3)
% 7.25/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 7.25/1.48      | u1_struct_0(X4) != u1_struct_0(sK1)
% 7.25/1.48      | u1_struct_0(X1) != u1_struct_0(sK3)
% 7.25/1.48      | sK4 != X3 ),
% 7.25/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_341,plain,
% 7.25/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.25/1.48      | ~ m1_pre_topc(X0,X2)
% 7.25/1.48      | ~ m1_pre_topc(X1,X2)
% 7.25/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 7.25/1.48      | v2_struct_0(X3)
% 7.25/1.48      | v2_struct_0(X2)
% 7.25/1.48      | ~ v2_pre_topc(X2)
% 7.25/1.48      | ~ v2_pre_topc(X3)
% 7.25/1.48      | ~ l1_pre_topc(X2)
% 7.25/1.48      | ~ l1_pre_topc(X3)
% 7.25/1.48      | ~ v1_funct_1(sK4)
% 7.25/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 7.25/1.48      | u1_struct_0(X3) != u1_struct_0(sK1)
% 7.25/1.48      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 7.25/1.48      inference(unflattening,[status(thm)],[c_340]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_20,negated_conjecture,
% 7.25/1.48      ( v1_funct_1(sK4) ),
% 7.25/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_345,plain,
% 7.25/1.48      ( ~ l1_pre_topc(X3)
% 7.25/1.48      | ~ l1_pre_topc(X2)
% 7.25/1.48      | ~ v2_pre_topc(X3)
% 7.25/1.48      | ~ v2_pre_topc(X2)
% 7.25/1.48      | v2_struct_0(X2)
% 7.25/1.48      | v2_struct_0(X3)
% 7.25/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 7.25/1.48      | ~ m1_pre_topc(X1,X2)
% 7.25/1.48      | ~ m1_pre_topc(X0,X2)
% 7.25/1.48      | ~ m1_pre_topc(X0,X1)
% 7.25/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 7.25/1.48      | u1_struct_0(X3) != u1_struct_0(sK1)
% 7.25/1.48      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 7.25/1.48      inference(global_propositional_subsumption,[status(thm)],[c_341,c_20]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_346,plain,
% 7.25/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.25/1.48      | ~ m1_pre_topc(X0,X2)
% 7.25/1.48      | ~ m1_pre_topc(X1,X2)
% 7.25/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 7.25/1.48      | v2_struct_0(X2)
% 7.25/1.48      | v2_struct_0(X3)
% 7.25/1.48      | ~ v2_pre_topc(X2)
% 7.25/1.48      | ~ v2_pre_topc(X3)
% 7.25/1.48      | ~ l1_pre_topc(X2)
% 7.25/1.48      | ~ l1_pre_topc(X3)
% 7.25/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 7.25/1.48      | u1_struct_0(X3) != u1_struct_0(sK1)
% 7.25/1.48      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 7.25/1.48      inference(renaming,[status(thm)],[c_345]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_589,plain,
% 7.25/1.48      ( ~ m1_pre_topc(X0_56,X1_56)
% 7.25/1.48      | ~ m1_pre_topc(X0_56,X2_56)
% 7.25/1.48      | ~ m1_pre_topc(X1_56,X2_56)
% 7.25/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X3_56))))
% 7.25/1.48      | v2_struct_0(X2_56)
% 7.25/1.48      | v2_struct_0(X3_56)
% 7.25/1.48      | ~ v2_pre_topc(X2_56)
% 7.25/1.48      | ~ v2_pre_topc(X3_56)
% 7.25/1.48      | ~ l1_pre_topc(X2_56)
% 7.25/1.48      | ~ l1_pre_topc(X3_56)
% 7.25/1.48      | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(X3_56),sK4,u1_struct_0(X0_56)) = k3_tmap_1(X2_56,X3_56,X1_56,X0_56,sK4)
% 7.25/1.48      | u1_struct_0(X3_56) != u1_struct_0(sK1)
% 7.25/1.48      | u1_struct_0(X1_56) != u1_struct_0(sK3) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_346]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1106,plain,
% 7.25/1.48      ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),sK4,u1_struct_0(X2_56)) = k3_tmap_1(X3_56,X1_56,X0_56,X2_56,sK4)
% 7.25/1.48      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 7.25/1.48      | u1_struct_0(X0_56) != u1_struct_0(sK3)
% 7.25/1.48      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X2_56,X3_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X0_56,X3_56) != iProver_top
% 7.25/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 7.25/1.48      | v2_struct_0(X1_56) = iProver_top
% 7.25/1.48      | v2_struct_0(X3_56) = iProver_top
% 7.25/1.48      | v2_pre_topc(X1_56) != iProver_top
% 7.25/1.48      | v2_pre_topc(X3_56) != iProver_top
% 7.25/1.48      | l1_pre_topc(X1_56) != iProver_top
% 7.25/1.48      | l1_pre_topc(X3_56) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_589]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1805,plain,
% 7.25/1.48      ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK4,u1_struct_0(X1_56)) = k3_tmap_1(X2_56,sK1,X0_56,X1_56,sK4)
% 7.25/1.48      | u1_struct_0(X0_56) != u1_struct_0(sK3)
% 7.25/1.48      | m1_pre_topc(X0_56,X2_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X1_56,X2_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 7.25/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 7.25/1.48      | v2_struct_0(X2_56) = iProver_top
% 7.25/1.48      | v2_struct_0(sK1) = iProver_top
% 7.25/1.48      | v2_pre_topc(X2_56) != iProver_top
% 7.25/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.25/1.48      | l1_pre_topc(X2_56) != iProver_top
% 7.25/1.48      | l1_pre_topc(sK1) != iProver_top ),
% 7.25/1.48      inference(equality_resolution,[status(thm)],[c_1106]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_27,negated_conjecture,
% 7.25/1.48      ( ~ v2_struct_0(sK1) ),
% 7.25/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_34,plain,
% 7.25/1.48      ( v2_struct_0(sK1) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_26,negated_conjecture,
% 7.25/1.48      ( v2_pre_topc(sK1) ),
% 7.25/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_35,plain,
% 7.25/1.48      ( v2_pre_topc(sK1) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_25,negated_conjecture,
% 7.25/1.48      ( l1_pre_topc(sK1) ),
% 7.25/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_36,plain,
% 7.25/1.48      ( l1_pre_topc(sK1) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2031,plain,
% 7.25/1.48      ( l1_pre_topc(X2_56) != iProver_top
% 7.25/1.48      | v2_struct_0(X2_56) = iProver_top
% 7.25/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 7.25/1.48      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X1_56,X2_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X0_56,X2_56) != iProver_top
% 7.25/1.48      | u1_struct_0(X0_56) != u1_struct_0(sK3)
% 7.25/1.48      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK4,u1_struct_0(X1_56)) = k3_tmap_1(X2_56,sK1,X0_56,X1_56,sK4)
% 7.25/1.48      | v2_pre_topc(X2_56) != iProver_top ),
% 7.25/1.48      inference(global_propositional_subsumption,
% 7.25/1.48                [status(thm)],
% 7.25/1.48                [c_1805,c_34,c_35,c_36]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2032,plain,
% 7.25/1.48      ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK4,u1_struct_0(X1_56)) = k3_tmap_1(X2_56,sK1,X0_56,X1_56,sK4)
% 7.25/1.48      | u1_struct_0(X0_56) != u1_struct_0(sK3)
% 7.25/1.48      | m1_pre_topc(X0_56,X2_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X1_56,X2_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 7.25/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 7.25/1.48      | v2_struct_0(X2_56) = iProver_top
% 7.25/1.48      | v2_pre_topc(X2_56) != iProver_top
% 7.25/1.48      | l1_pre_topc(X2_56) != iProver_top ),
% 7.25/1.48      inference(renaming,[status(thm)],[c_2031]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2044,plain,
% 7.25/1.48      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_56)) = k3_tmap_1(X1_56,sK1,sK3,X0_56,sK4)
% 7.25/1.48      | m1_pre_topc(X0_56,X1_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X0_56,sK3) != iProver_top
% 7.25/1.48      | m1_pre_topc(sK3,X1_56) != iProver_top
% 7.25/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.25/1.48      | v2_struct_0(X1_56) = iProver_top
% 7.25/1.48      | v2_pre_topc(X1_56) != iProver_top
% 7.25/1.48      | l1_pre_topc(X1_56) != iProver_top ),
% 7.25/1.48      inference(equality_resolution,[status(thm)],[c_2032]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_12,plain,
% 7.25/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.48      | ~ v1_funct_1(X0)
% 7.25/1.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.25/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_392,plain,
% 7.25/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.25/1.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 7.25/1.48      | sK4 != X0 ),
% 7.25/1.48      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_393,plain,
% 7.25/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.25/1.48      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 7.25/1.48      inference(unflattening,[status(thm)],[c_392]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_588,plain,
% 7.25/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.25/1.48      | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_393]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1107,plain,
% 7.25/1.48      ( k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54)
% 7.25/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1709,plain,
% 7.25/1.48      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_1094,c_1107]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2045,plain,
% 7.25/1.48      ( k3_tmap_1(X0_56,sK1,sK3,X1_56,sK4) = k7_relat_1(sK4,u1_struct_0(X1_56))
% 7.25/1.48      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X1_56,sK3) != iProver_top
% 7.25/1.48      | m1_pre_topc(sK3,X0_56) != iProver_top
% 7.25/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.25/1.48      | v2_struct_0(X0_56) = iProver_top
% 7.25/1.48      | v2_pre_topc(X0_56) != iProver_top
% 7.25/1.48      | l1_pre_topc(X0_56) != iProver_top ),
% 7.25/1.48      inference(demodulation,[status(thm)],[c_2044,c_1709]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2050,plain,
% 7.25/1.48      ( m1_pre_topc(sK3,X0_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X1_56,sK3) != iProver_top
% 7.25/1.48      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 7.25/1.48      | k3_tmap_1(X0_56,sK1,sK3,X1_56,sK4) = k7_relat_1(sK4,u1_struct_0(X1_56))
% 7.25/1.48      | v2_struct_0(X0_56) = iProver_top
% 7.25/1.48      | v2_pre_topc(X0_56) != iProver_top
% 7.25/1.48      | l1_pre_topc(X0_56) != iProver_top ),
% 7.25/1.48      inference(global_propositional_subsumption,[status(thm)],[c_2045,c_43]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2051,plain,
% 7.25/1.48      ( k3_tmap_1(X0_56,sK1,sK3,X1_56,sK4) = k7_relat_1(sK4,u1_struct_0(X1_56))
% 7.25/1.48      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 7.25/1.48      | m1_pre_topc(X1_56,sK3) != iProver_top
% 7.25/1.48      | m1_pre_topc(sK3,X0_56) != iProver_top
% 7.25/1.48      | v2_struct_0(X0_56) = iProver_top
% 7.25/1.48      | v2_pre_topc(X0_56) != iProver_top
% 7.25/1.48      | l1_pre_topc(X0_56) != iProver_top ),
% 7.25/1.48      inference(renaming,[status(thm)],[c_2050]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2065,plain,
% 7.25/1.48      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 7.25/1.48      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.25/1.48      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.25/1.48      | v2_struct_0(sK0) = iProver_top
% 7.25/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.25/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_1097,c_2051]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_30,negated_conjecture,
% 7.25/1.48      ( ~ v2_struct_0(sK0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_31,plain,
% 7.25/1.48      ( v2_struct_0(sK0) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_29,negated_conjecture,
% 7.25/1.48      ( v2_pre_topc(sK0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_32,plain,
% 7.25/1.48      ( v2_pre_topc(sK0) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_28,negated_conjecture,
% 7.25/1.48      ( l1_pre_topc(sK0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_33,plain,
% 7.25/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_21,negated_conjecture,
% 7.25/1.48      ( m1_pre_topc(sK3,sK0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_40,plain,
% 7.25/1.48      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_17,negated_conjecture,
% 7.25/1.48      ( m1_pre_topc(sK2,sK3) ),
% 7.25/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_44,plain,
% 7.25/1.48      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2216,plain,
% 7.25/1.48      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 7.25/1.48      inference(global_propositional_subsumption,
% 7.25/1.48                [status(thm)],
% 7.25/1.48                [c_2065,c_31,c_32,c_33,c_40,c_44]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1918,plain,
% 7.25/1.48      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k9_relat_1(sK4,X0_54) ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_1094,c_1088]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_14,negated_conjecture,
% 7.25/1.48      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 7.25/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_605,negated_conjecture,
% 7.25/1.48      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_14]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1978,plain,
% 7.25/1.48      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
% 7.25/1.48      inference(demodulation,[status(thm)],[c_1918,c_605]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2219,plain,
% 7.25/1.48      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
% 7.25/1.48      inference(demodulation,[status(thm)],[c_2216,c_1978]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_16246,plain,
% 7.25/1.48      ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
% 7.25/1.48      inference(demodulation,[status(thm)],[c_16242,c_2219]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_0,plain,
% 7.25/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f43]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_614,plain,
% 7.25/1.48      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.25/1.48      | ~ v1_relat_1(X1_54)
% 7.25/1.48      | v1_relat_1(X0_54) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1082,plain,
% 7.25/1.48      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 7.25/1.48      | v1_relat_1(X1_54) != iProver_top
% 7.25/1.48      | v1_relat_1(X0_54) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1557,plain,
% 7.25/1.48      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
% 7.25/1.48      | v1_relat_1(sK4) = iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_1094,c_1082]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1630,plain,
% 7.25/1.48      ( v1_relat_1(sK4) = iProver_top ),
% 7.25/1.48      inference(global_propositional_subsumption,
% 7.25/1.48                [status(thm)],
% 7.25/1.48                [c_1557,c_43,c_1288]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_15,negated_conjecture,
% 7.25/1.48      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 7.25/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_604,negated_conjecture,
% 7.25/1.48      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_15]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1091,plain,
% 7.25/1.48      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_4,plain,
% 7.25/1.48      ( ~ r1_tarski(X0,X1)
% 7.25/1.48      | ~ v1_relat_1(X2)
% 7.25/1.48      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 7.25/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_612,plain,
% 7.25/1.48      ( ~ r1_tarski(X0_54,X1_54)
% 7.25/1.48      | ~ v1_relat_1(X2_54)
% 7.25/1.48      | k9_relat_1(k7_relat_1(X2_54,X1_54),X0_54) = k9_relat_1(X2_54,X0_54) ),
% 7.25/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1084,plain,
% 7.25/1.48      ( k9_relat_1(k7_relat_1(X0_54,X1_54),X2_54) = k9_relat_1(X0_54,X2_54)
% 7.25/1.48      | r1_tarski(X2_54,X1_54) != iProver_top
% 7.25/1.48      | v1_relat_1(X0_54) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2275,plain,
% 7.25/1.48      ( k9_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_54,sK5)
% 7.25/1.48      | v1_relat_1(X0_54) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_1091,c_1084]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_2455,plain,
% 7.25/1.48      ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k9_relat_1(sK4,sK5) ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_1630,c_2275]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_16247,plain,
% 7.25/1.48      ( k9_relat_1(sK4,sK5) != k9_relat_1(sK4,sK5) ),
% 7.25/1.48      inference(light_normalisation,[status(thm)],[c_16246,c_2455]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_16248,plain,
% 7.25/1.48      ( $false ),
% 7.25/1.48      inference(equality_resolution_simp,[status(thm)],[c_16247]) ).
% 7.25/1.48  
% 7.25/1.48  
% 7.25/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.25/1.48  
% 7.25/1.48  ------                               Statistics
% 7.25/1.48  
% 7.25/1.48  ------ General
% 7.25/1.48  
% 7.25/1.48  abstr_ref_over_cycles:                  0
% 7.25/1.48  abstr_ref_under_cycles:                 0
% 7.25/1.48  gc_basic_clause_elim:                   0
% 7.25/1.48  forced_gc_time:                         0
% 7.25/1.48  parsing_time:                           0.011
% 7.25/1.48  unif_index_cands_time:                  0.
% 7.25/1.48  unif_index_add_time:                    0.
% 7.25/1.48  orderings_time:                         0.
% 7.25/1.48  out_proof_time:                         0.026
% 7.25/1.48  total_time:                             0.537
% 7.25/1.48  num_of_symbols:                         61
% 7.25/1.48  num_of_terms:                           12653
% 7.25/1.48  
% 7.25/1.48  ------ Preprocessing
% 7.25/1.48  
% 7.25/1.48  num_of_splits:                          0
% 7.25/1.48  num_of_split_atoms:                     0
% 7.25/1.48  num_of_reused_defs:                     0
% 7.25/1.48  num_eq_ax_congr_red:                    23
% 7.25/1.48  num_of_sem_filtered_clauses:            1
% 7.25/1.48  num_of_subtypes:                        4
% 7.25/1.48  monotx_restored_types:                  0
% 7.25/1.48  sat_num_of_epr_types:                   0
% 7.25/1.48  sat_num_of_non_cyclic_types:            0
% 7.25/1.48  sat_guarded_non_collapsed_types:        0
% 7.25/1.48  num_pure_diseq_elim:                    0
% 7.25/1.48  simp_replaced_by:                       0
% 7.25/1.48  res_preprocessed:                       145
% 7.25/1.48  prep_upred:                             0
% 7.25/1.49  prep_unflattend:                        2
% 7.25/1.49  smt_new_axioms:                         0
% 7.25/1.49  pred_elim_cands:                        7
% 7.25/1.49  pred_elim:                              3
% 7.25/1.49  pred_elim_cl:                           4
% 7.25/1.49  pred_elim_cycles:                       5
% 7.25/1.49  merged_defs:                            0
% 7.25/1.49  merged_defs_ncl:                        0
% 7.25/1.49  bin_hyper_res:                          0
% 7.25/1.49  prep_cycles:                            4
% 7.25/1.49  pred_elim_time:                         0.004
% 7.25/1.49  splitting_time:                         0.
% 7.25/1.49  sem_filter_time:                        0.
% 7.25/1.49  monotx_time:                            0.
% 7.25/1.49  subtype_inf_time:                       0.
% 7.25/1.49  
% 7.25/1.49  ------ Problem properties
% 7.25/1.49  
% 7.25/1.49  clauses:                                27
% 7.25/1.49  conjectures:                            15
% 7.25/1.49  epr:                                    11
% 7.25/1.49  horn:                                   26
% 7.25/1.49  ground:                                 15
% 7.25/1.49  unary:                                  16
% 7.25/1.49  binary:                                 6
% 7.25/1.49  lits:                                   54
% 7.25/1.49  lits_eq:                                7
% 7.25/1.49  fd_pure:                                0
% 7.25/1.49  fd_pseudo:                              0
% 7.25/1.49  fd_cond:                                0
% 7.25/1.49  fd_pseudo_cond:                         0
% 7.25/1.49  ac_symbols:                             0
% 7.25/1.49  
% 7.25/1.49  ------ Propositional Solver
% 7.25/1.49  
% 7.25/1.49  prop_solver_calls:                      33
% 7.25/1.49  prop_fast_solver_calls:                 1166
% 7.25/1.49  smt_solver_calls:                       0
% 7.25/1.49  smt_fast_solver_calls:                  0
% 7.25/1.49  prop_num_of_clauses:                    4551
% 7.25/1.49  prop_preprocess_simplified:             11309
% 7.25/1.49  prop_fo_subsumed:                       28
% 7.25/1.49  prop_solver_time:                       0.
% 7.25/1.49  smt_solver_time:                        0.
% 7.25/1.49  smt_fast_solver_time:                   0.
% 7.25/1.49  prop_fast_solver_time:                  0.
% 7.25/1.49  prop_unsat_core_time:                   0.
% 7.25/1.49  
% 7.25/1.49  ------ QBF
% 7.25/1.49  
% 7.25/1.49  qbf_q_res:                              0
% 7.25/1.49  qbf_num_tautologies:                    0
% 7.25/1.49  qbf_prep_cycles:                        0
% 7.25/1.49  
% 7.25/1.49  ------ BMC1
% 7.25/1.49  
% 7.25/1.49  bmc1_current_bound:                     -1
% 7.25/1.49  bmc1_last_solved_bound:                 -1
% 7.25/1.49  bmc1_unsat_core_size:                   -1
% 7.25/1.49  bmc1_unsat_core_parents_size:           -1
% 7.25/1.49  bmc1_merge_next_fun:                    0
% 7.25/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.25/1.49  
% 7.25/1.49  ------ Instantiation
% 7.25/1.49  
% 7.25/1.49  inst_num_of_clauses:                    1764
% 7.25/1.49  inst_num_in_passive:                    456
% 7.25/1.49  inst_num_in_active:                     992
% 7.25/1.49  inst_num_in_unprocessed:                316
% 7.25/1.49  inst_num_of_loops:                      1030
% 7.25/1.49  inst_num_of_learning_restarts:          0
% 7.25/1.49  inst_num_moves_active_passive:          32
% 7.25/1.49  inst_lit_activity:                      0
% 7.25/1.49  inst_lit_activity_moves:                0
% 7.25/1.49  inst_num_tautologies:                   0
% 7.25/1.49  inst_num_prop_implied:                  0
% 7.25/1.49  inst_num_existing_simplified:           0
% 7.25/1.49  inst_num_eq_res_simplified:             0
% 7.25/1.49  inst_num_child_elim:                    0
% 7.25/1.49  inst_num_of_dismatching_blockings:      1701
% 7.25/1.49  inst_num_of_non_proper_insts:           3086
% 7.25/1.49  inst_num_of_duplicates:                 0
% 7.25/1.49  inst_inst_num_from_inst_to_res:         0
% 7.25/1.49  inst_dismatching_checking_time:         0.
% 7.25/1.49  
% 7.25/1.49  ------ Resolution
% 7.25/1.49  
% 7.25/1.49  res_num_of_clauses:                     0
% 7.25/1.49  res_num_in_passive:                     0
% 7.25/1.49  res_num_in_active:                      0
% 7.25/1.49  res_num_of_loops:                       149
% 7.25/1.49  res_forward_subset_subsumed:            568
% 7.25/1.49  res_backward_subset_subsumed:           2
% 7.25/1.49  res_forward_subsumed:                   0
% 7.25/1.49  res_backward_subsumed:                  0
% 7.25/1.49  res_forward_subsumption_resolution:     1
% 7.25/1.49  res_backward_subsumption_resolution:    0
% 7.25/1.49  res_clause_to_clause_subsumption:       1477
% 7.25/1.49  res_orphan_elimination:                 0
% 7.25/1.49  res_tautology_del:                      454
% 7.25/1.49  res_num_eq_res_simplified:              0
% 7.25/1.49  res_num_sel_changes:                    0
% 7.25/1.49  res_moves_from_active_to_pass:          0
% 7.25/1.49  
% 7.25/1.49  ------ Superposition
% 7.25/1.49  
% 7.25/1.49  sup_time_total:                         0.
% 7.25/1.49  sup_time_generating:                    0.
% 7.25/1.49  sup_time_sim_full:                      0.
% 7.25/1.49  sup_time_sim_immed:                     0.
% 7.25/1.49  
% 7.25/1.49  sup_num_of_clauses:                     390
% 7.25/1.49  sup_num_in_active:                      201
% 7.25/1.49  sup_num_in_passive:                     189
% 7.25/1.49  sup_num_of_loops:                       204
% 7.25/1.49  sup_fw_superposition:                   210
% 7.25/1.49  sup_bw_superposition:                   183
% 7.25/1.49  sup_immediate_simplified:               27
% 7.25/1.49  sup_given_eliminated:                   0
% 7.25/1.49  comparisons_done:                       0
% 7.25/1.49  comparisons_avoided:                    0
% 7.25/1.49  
% 7.25/1.49  ------ Simplifications
% 7.25/1.49  
% 7.25/1.49  
% 7.25/1.49  sim_fw_subset_subsumed:                 8
% 7.25/1.49  sim_bw_subset_subsumed:                 6
% 7.25/1.49  sim_fw_subsumed:                        0
% 7.25/1.49  sim_bw_subsumed:                        12
% 7.25/1.49  sim_fw_subsumption_res:                 2
% 7.25/1.49  sim_bw_subsumption_res:                 0
% 7.25/1.49  sim_tautology_del:                      3
% 7.25/1.49  sim_eq_tautology_del:                   0
% 7.25/1.49  sim_eq_res_simp:                        0
% 7.25/1.49  sim_fw_demodulated:                     1
% 7.25/1.49  sim_bw_demodulated:                     3
% 7.25/1.49  sim_light_normalised:                   1
% 7.25/1.49  sim_joinable_taut:                      0
% 7.25/1.49  sim_joinable_simp:                      0
% 7.25/1.49  sim_ac_normalised:                      0
% 7.25/1.49  sim_smt_subsumption:                    0
% 7.25/1.49  
%------------------------------------------------------------------------------
