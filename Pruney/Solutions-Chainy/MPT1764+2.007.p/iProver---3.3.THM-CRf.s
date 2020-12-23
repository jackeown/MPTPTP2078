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
% DateTime   : Thu Dec  3 12:22:56 EST 2020

% Result     : Theorem 11.97s
% Output     : CNFRefutation 11.97s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 699 expanded)
%              Number of clauses        :  116 ( 227 expanded)
%              Number of leaves         :   19 ( 246 expanded)
%              Depth                    :   25
%              Number of atoms          :  703 (7123 expanded)
%              Number of equality atoms :  223 ( 794 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & r1_tarski(X5,u1_struct_0(X2))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
     => ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5)
        & r1_tarski(sK5,u1_struct_0(X2))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f37,f36,f35,f34,f33,f32])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_704,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1428,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | k7_relset_1(X1_54,X2_54,X0_54,X3_54) = k9_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1420,plain,
    ( k7_relset_1(X0_54,X1_54,X2_54,X3_54) = k9_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_2448,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k9_relat_1(sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_1428,c_1420])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | m1_subset_1(k7_relset_1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(X2_54)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1419,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(k7_relset_1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(X2_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_2803,plain,
    ( m1_subset_1(k9_relat_1(sK4,X0_54),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2448,c_1419])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4129,plain,
    ( m1_subset_1(k9_relat_1(sK4,X0_54),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2803,c_43])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_719,plain,
    ( r1_tarski(X0_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1414,plain,
    ( r1_tarski(X0_54,X1_54) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_4136,plain,
    ( r1_tarski(k9_relat_1(sK4,X0_54),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4129,c_1414])).

cnf(c_2316,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1428,c_1414])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_215,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_270,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_215])).

cnf(c_692,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ v1_relat_1(X1_54)
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_270])).

cnf(c_1440,plain,
    ( r1_tarski(X0_54,X1_54) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_3732,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_1440])).

cnf(c_1650,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1651,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1650])).

cnf(c_1637,plain,
    ( ~ r1_tarski(X0_54,k2_zfmisc_1(X1_54,X2_54))
    | v1_relat_1(X0_54)
    | ~ v1_relat_1(k2_zfmisc_1(X1_54,X2_54)) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_2093,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_2094,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2093])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_718,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2256,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_2257,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2256])).

cnf(c_3927,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3732,c_43,c_1651,c_2094,c_2257])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_717,plain,
    ( ~ v1_relat_1(X0_54)
    | k2_relat_1(k7_relat_1(X0_54,X1_54)) = k9_relat_1(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1416,plain,
    ( k2_relat_1(k7_relat_1(X0_54,X1_54)) = k9_relat_1(X0_54,X1_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_3934,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0_54)) = k9_relat_1(sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_3927,c_1416])).

cnf(c_6,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_715,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X1_54)),X1_54)
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1418,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X1_54)),X1_54) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_9,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_712,plain,
    ( ~ r1_tarski(k1_relat_1(X0_54),X1_54)
    | ~ r1_tarski(k2_relat_1(X0_54),X2_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1421,plain,
    ( r1_tarski(k1_relat_1(X0_54),X1_54) != iProver_top
    | r1_tarski(k2_relat_1(X0_54),X2_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_3522,plain,
    ( k7_relset_1(X0_54,X1_54,X2_54,X3_54) = k9_relat_1(X2_54,X3_54)
    | r1_tarski(k1_relat_1(X2_54),X0_54) != iProver_top
    | r1_tarski(k2_relat_1(X2_54),X1_54) != iProver_top
    | v1_relat_1(X2_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1420])).

cnf(c_16116,plain,
    ( k7_relset_1(X0_54,X1_54,k7_relat_1(X2_54,X0_54),X3_54) = k9_relat_1(k7_relat_1(X2_54,X0_54),X3_54)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_54,X0_54)),X1_54) != iProver_top
    | v1_relat_1(X2_54) != iProver_top
    | v1_relat_1(k7_relat_1(X2_54,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_3522])).

cnf(c_38819,plain,
    ( k7_relset_1(X0_54,X1_54,k7_relat_1(sK4,X0_54),X2_54) = k9_relat_1(k7_relat_1(sK4,X0_54),X2_54)
    | r1_tarski(k9_relat_1(sK4,X0_54),X1_54) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0_54)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3934,c_16116])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1424,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_2933,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1428,c_1424])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1717,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_3174,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2933,c_20,c_18,c_1717])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_711,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | m1_subset_1(k2_partfun1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1422,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(k2_partfun1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_3211,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3174,c_1422])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4210,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3211,c_41,c_43])).

cnf(c_4218,plain,
    ( r1_tarski(k7_relat_1(sK4,X0_54),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4210,c_1414])).

cnf(c_4468,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0_54)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4218,c_1440])).

cnf(c_47422,plain,
    ( k7_relset_1(X0_54,X1_54,k7_relat_1(sK4,X0_54),X2_54) = k9_relat_1(k7_relat_1(sK4,X0_54),X2_54)
    | r1_tarski(k9_relat_1(sK4,X0_54),X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38819,c_43,c_1651,c_2094,c_2257,c_4468])).

cnf(c_47431,plain,
    ( k7_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK4,X0_54),X1_54) = k9_relat_1(k7_relat_1(sK4,X0_54),X1_54) ),
    inference(superposition,[status(thm)],[c_4136,c_47422])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_700,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1432,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

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
    inference(cnf_transformation,[],[f52])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_382,plain,
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

cnf(c_383,plain,
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
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_387,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_20])).

cnf(c_388,plain,
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
    inference(renaming,[status(thm)],[c_387])).

cnf(c_691,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_pre_topc(X1_53,X2_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X3_53))))
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ v2_pre_topc(X2_53)
    | ~ v2_pre_topc(X3_53)
    | ~ l1_pre_topc(X2_53)
    | ~ l1_pre_topc(X3_53)
    | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X3_53),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X2_53,X3_53,X1_53,X0_53,sK4)
    | u1_struct_0(X3_53) != u1_struct_0(sK1)
    | u1_struct_0(X1_53) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_388])).

cnf(c_1441,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_2089,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1441])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_35,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_36,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2183,plain,
    ( l1_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
    | v2_pre_topc(X2_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2089,c_34,c_35,c_36])).

cnf(c_2184,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
    | u1_struct_0(X0_53) != u1_struct_0(sK3)
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2183])).

cnf(c_2196,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2184])).

cnf(c_2201,plain,
    ( m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2196,c_43])).

cnf(c_2202,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2201])).

cnf(c_2216,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_2202])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_40,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_44,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2649,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2216,c_31,c_32,c_33,c_40,c_44])).

cnf(c_3180,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_3174,c_2649])).

cnf(c_14,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_708,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2588,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_2448,c_708])).

cnf(c_3431,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_3180,c_2588])).

cnf(c_47447,plain,
    ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_47431,c_3431])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_707,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1425,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_716,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ v1_relat_1(X2_54)
    | k9_relat_1(k7_relat_1(X2_54,X1_54),X0_54) = k9_relat_1(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1417,plain,
    ( k9_relat_1(k7_relat_1(X0_54,X1_54),X2_54) = k9_relat_1(X0_54,X2_54)
    | r1_tarski(X2_54,X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_2766,plain,
    ( k9_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_54,sK5)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1425,c_1417])).

cnf(c_3933,plain,
    ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k9_relat_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_3927,c_2766])).

cnf(c_47448,plain,
    ( k9_relat_1(sK4,sK5) != k9_relat_1(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_47447,c_3933])).

cnf(c_47449,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_47448])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.97/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.97/2.00  
% 11.97/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.97/2.00  
% 11.97/2.00  ------  iProver source info
% 11.97/2.00  
% 11.97/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.97/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.97/2.00  git: non_committed_changes: false
% 11.97/2.00  git: last_make_outside_of_git: false
% 11.97/2.00  
% 11.97/2.00  ------ 
% 11.97/2.00  
% 11.97/2.00  ------ Input Options
% 11.97/2.00  
% 11.97/2.00  --out_options                           all
% 11.97/2.00  --tptp_safe_out                         true
% 11.97/2.00  --problem_path                          ""
% 11.97/2.00  --include_path                          ""
% 11.97/2.00  --clausifier                            res/vclausify_rel
% 11.97/2.00  --clausifier_options                    --mode clausify
% 11.97/2.00  --stdin                                 false
% 11.97/2.00  --stats_out                             all
% 11.97/2.00  
% 11.97/2.00  ------ General Options
% 11.97/2.00  
% 11.97/2.00  --fof                                   false
% 11.97/2.00  --time_out_real                         305.
% 11.97/2.00  --time_out_virtual                      -1.
% 11.97/2.00  --symbol_type_check                     false
% 11.97/2.00  --clausify_out                          false
% 11.97/2.00  --sig_cnt_out                           false
% 11.97/2.00  --trig_cnt_out                          false
% 11.97/2.00  --trig_cnt_out_tolerance                1.
% 11.97/2.00  --trig_cnt_out_sk_spl                   false
% 11.97/2.00  --abstr_cl_out                          false
% 11.97/2.00  
% 11.97/2.00  ------ Global Options
% 11.97/2.00  
% 11.97/2.00  --schedule                              default
% 11.97/2.00  --add_important_lit                     false
% 11.97/2.00  --prop_solver_per_cl                    1000
% 11.97/2.00  --min_unsat_core                        false
% 11.97/2.00  --soft_assumptions                      false
% 11.97/2.00  --soft_lemma_size                       3
% 11.97/2.00  --prop_impl_unit_size                   0
% 11.97/2.00  --prop_impl_unit                        []
% 11.97/2.00  --share_sel_clauses                     true
% 11.97/2.00  --reset_solvers                         false
% 11.97/2.00  --bc_imp_inh                            [conj_cone]
% 11.97/2.00  --conj_cone_tolerance                   3.
% 11.97/2.00  --extra_neg_conj                        none
% 11.97/2.00  --large_theory_mode                     true
% 11.97/2.00  --prolific_symb_bound                   200
% 11.97/2.00  --lt_threshold                          2000
% 11.97/2.00  --clause_weak_htbl                      true
% 11.97/2.00  --gc_record_bc_elim                     false
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing Options
% 11.97/2.00  
% 11.97/2.00  --preprocessing_flag                    true
% 11.97/2.00  --time_out_prep_mult                    0.1
% 11.97/2.00  --splitting_mode                        input
% 11.97/2.00  --splitting_grd                         true
% 11.97/2.00  --splitting_cvd                         false
% 11.97/2.00  --splitting_cvd_svl                     false
% 11.97/2.00  --splitting_nvd                         32
% 11.97/2.00  --sub_typing                            true
% 11.97/2.00  --prep_gs_sim                           true
% 11.97/2.00  --prep_unflatten                        true
% 11.97/2.00  --prep_res_sim                          true
% 11.97/2.00  --prep_upred                            true
% 11.97/2.00  --prep_sem_filter                       exhaustive
% 11.97/2.00  --prep_sem_filter_out                   false
% 11.97/2.00  --pred_elim                             true
% 11.97/2.00  --res_sim_input                         true
% 11.97/2.00  --eq_ax_congr_red                       true
% 11.97/2.00  --pure_diseq_elim                       true
% 11.97/2.00  --brand_transform                       false
% 11.97/2.00  --non_eq_to_eq                          false
% 11.97/2.00  --prep_def_merge                        true
% 11.97/2.00  --prep_def_merge_prop_impl              false
% 11.97/2.00  --prep_def_merge_mbd                    true
% 11.97/2.00  --prep_def_merge_tr_red                 false
% 11.97/2.00  --prep_def_merge_tr_cl                  false
% 11.97/2.00  --smt_preprocessing                     true
% 11.97/2.00  --smt_ac_axioms                         fast
% 11.97/2.00  --preprocessed_out                      false
% 11.97/2.00  --preprocessed_stats                    false
% 11.97/2.00  
% 11.97/2.00  ------ Abstraction refinement Options
% 11.97/2.00  
% 11.97/2.00  --abstr_ref                             []
% 11.97/2.00  --abstr_ref_prep                        false
% 11.97/2.00  --abstr_ref_until_sat                   false
% 11.97/2.00  --abstr_ref_sig_restrict                funpre
% 11.97/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.97/2.00  --abstr_ref_under                       []
% 11.97/2.00  
% 11.97/2.00  ------ SAT Options
% 11.97/2.00  
% 11.97/2.00  --sat_mode                              false
% 11.97/2.00  --sat_fm_restart_options                ""
% 11.97/2.00  --sat_gr_def                            false
% 11.97/2.00  --sat_epr_types                         true
% 11.97/2.00  --sat_non_cyclic_types                  false
% 11.97/2.00  --sat_finite_models                     false
% 11.97/2.00  --sat_fm_lemmas                         false
% 11.97/2.00  --sat_fm_prep                           false
% 11.97/2.00  --sat_fm_uc_incr                        true
% 11.97/2.00  --sat_out_model                         small
% 11.97/2.00  --sat_out_clauses                       false
% 11.97/2.00  
% 11.97/2.00  ------ QBF Options
% 11.97/2.00  
% 11.97/2.00  --qbf_mode                              false
% 11.97/2.00  --qbf_elim_univ                         false
% 11.97/2.00  --qbf_dom_inst                          none
% 11.97/2.00  --qbf_dom_pre_inst                      false
% 11.97/2.00  --qbf_sk_in                             false
% 11.97/2.00  --qbf_pred_elim                         true
% 11.97/2.00  --qbf_split                             512
% 11.97/2.00  
% 11.97/2.00  ------ BMC1 Options
% 11.97/2.00  
% 11.97/2.00  --bmc1_incremental                      false
% 11.97/2.00  --bmc1_axioms                           reachable_all
% 11.97/2.00  --bmc1_min_bound                        0
% 11.97/2.00  --bmc1_max_bound                        -1
% 11.97/2.00  --bmc1_max_bound_default                -1
% 11.97/2.00  --bmc1_symbol_reachability              true
% 11.97/2.00  --bmc1_property_lemmas                  false
% 11.97/2.00  --bmc1_k_induction                      false
% 11.97/2.00  --bmc1_non_equiv_states                 false
% 11.97/2.00  --bmc1_deadlock                         false
% 11.97/2.00  --bmc1_ucm                              false
% 11.97/2.00  --bmc1_add_unsat_core                   none
% 11.97/2.00  --bmc1_unsat_core_children              false
% 11.97/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.97/2.00  --bmc1_out_stat                         full
% 11.97/2.00  --bmc1_ground_init                      false
% 11.97/2.00  --bmc1_pre_inst_next_state              false
% 11.97/2.00  --bmc1_pre_inst_state                   false
% 11.97/2.00  --bmc1_pre_inst_reach_state             false
% 11.97/2.00  --bmc1_out_unsat_core                   false
% 11.97/2.00  --bmc1_aig_witness_out                  false
% 11.97/2.00  --bmc1_verbose                          false
% 11.97/2.00  --bmc1_dump_clauses_tptp                false
% 11.97/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.97/2.00  --bmc1_dump_file                        -
% 11.97/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.97/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.97/2.00  --bmc1_ucm_extend_mode                  1
% 11.97/2.00  --bmc1_ucm_init_mode                    2
% 11.97/2.00  --bmc1_ucm_cone_mode                    none
% 11.97/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.97/2.00  --bmc1_ucm_relax_model                  4
% 11.97/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.97/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.97/2.00  --bmc1_ucm_layered_model                none
% 11.97/2.00  --bmc1_ucm_max_lemma_size               10
% 11.97/2.00  
% 11.97/2.00  ------ AIG Options
% 11.97/2.00  
% 11.97/2.00  --aig_mode                              false
% 11.97/2.00  
% 11.97/2.00  ------ Instantiation Options
% 11.97/2.00  
% 11.97/2.00  --instantiation_flag                    true
% 11.97/2.00  --inst_sos_flag                         false
% 11.97/2.00  --inst_sos_phase                        true
% 11.97/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.97/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.97/2.00  --inst_lit_sel_side                     num_symb
% 11.97/2.00  --inst_solver_per_active                1400
% 11.97/2.00  --inst_solver_calls_frac                1.
% 11.97/2.00  --inst_passive_queue_type               priority_queues
% 11.97/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.97/2.00  --inst_passive_queues_freq              [25;2]
% 11.97/2.00  --inst_dismatching                      true
% 11.97/2.00  --inst_eager_unprocessed_to_passive     true
% 11.97/2.00  --inst_prop_sim_given                   true
% 11.97/2.00  --inst_prop_sim_new                     false
% 11.97/2.00  --inst_subs_new                         false
% 11.97/2.00  --inst_eq_res_simp                      false
% 11.97/2.00  --inst_subs_given                       false
% 11.97/2.00  --inst_orphan_elimination               true
% 11.97/2.00  --inst_learning_loop_flag               true
% 11.97/2.00  --inst_learning_start                   3000
% 11.97/2.00  --inst_learning_factor                  2
% 11.97/2.00  --inst_start_prop_sim_after_learn       3
% 11.97/2.00  --inst_sel_renew                        solver
% 11.97/2.00  --inst_lit_activity_flag                true
% 11.97/2.00  --inst_restr_to_given                   false
% 11.97/2.00  --inst_activity_threshold               500
% 11.97/2.00  --inst_out_proof                        true
% 11.97/2.00  
% 11.97/2.00  ------ Resolution Options
% 11.97/2.00  
% 11.97/2.00  --resolution_flag                       true
% 11.97/2.00  --res_lit_sel                           adaptive
% 11.97/2.00  --res_lit_sel_side                      none
% 11.97/2.00  --res_ordering                          kbo
% 11.97/2.00  --res_to_prop_solver                    active
% 11.97/2.00  --res_prop_simpl_new                    false
% 11.97/2.00  --res_prop_simpl_given                  true
% 11.97/2.00  --res_passive_queue_type                priority_queues
% 11.97/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.97/2.00  --res_passive_queues_freq               [15;5]
% 11.97/2.00  --res_forward_subs                      full
% 11.97/2.00  --res_backward_subs                     full
% 11.97/2.00  --res_forward_subs_resolution           true
% 11.97/2.00  --res_backward_subs_resolution          true
% 11.97/2.00  --res_orphan_elimination                true
% 11.97/2.00  --res_time_limit                        2.
% 11.97/2.00  --res_out_proof                         true
% 11.97/2.00  
% 11.97/2.00  ------ Superposition Options
% 11.97/2.00  
% 11.97/2.00  --superposition_flag                    true
% 11.97/2.00  --sup_passive_queue_type                priority_queues
% 11.97/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.97/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.97/2.00  --demod_completeness_check              fast
% 11.97/2.00  --demod_use_ground                      true
% 11.97/2.00  --sup_to_prop_solver                    passive
% 11.97/2.00  --sup_prop_simpl_new                    true
% 11.97/2.00  --sup_prop_simpl_given                  true
% 11.97/2.00  --sup_fun_splitting                     false
% 11.97/2.00  --sup_smt_interval                      50000
% 11.97/2.00  
% 11.97/2.00  ------ Superposition Simplification Setup
% 11.97/2.00  
% 11.97/2.00  --sup_indices_passive                   []
% 11.97/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.97/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/2.00  --sup_full_bw                           [BwDemod]
% 11.97/2.00  --sup_immed_triv                        [TrivRules]
% 11.97/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/2.00  --sup_immed_bw_main                     []
% 11.97/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.97/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/2.00  
% 11.97/2.00  ------ Combination Options
% 11.97/2.00  
% 11.97/2.00  --comb_res_mult                         3
% 11.97/2.00  --comb_sup_mult                         2
% 11.97/2.00  --comb_inst_mult                        10
% 11.97/2.00  
% 11.97/2.00  ------ Debug Options
% 11.97/2.00  
% 11.97/2.00  --dbg_backtrace                         false
% 11.97/2.00  --dbg_dump_prop_clauses                 false
% 11.97/2.00  --dbg_dump_prop_clauses_file            -
% 11.97/2.00  --dbg_out_stat                          false
% 11.97/2.00  ------ Parsing...
% 11.97/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/2.00  ------ Proving...
% 11.97/2.00  ------ Problem Properties 
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  clauses                                 30
% 11.97/2.00  conjectures                             16
% 11.97/2.00  EPR                                     13
% 11.97/2.00  Horn                                    29
% 11.97/2.00  unary                                   17
% 11.97/2.00  binary                                  6
% 11.97/2.00  lits                                    61
% 11.97/2.00  lits eq                                 8
% 11.97/2.00  fd_pure                                 0
% 11.97/2.00  fd_pseudo                               0
% 11.97/2.00  fd_cond                                 0
% 11.97/2.00  fd_pseudo_cond                          0
% 11.97/2.00  AC symbols                              0
% 11.97/2.00  
% 11.97/2.00  ------ Schedule dynamic 5 is on 
% 11.97/2.00  
% 11.97/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ 
% 11.97/2.00  Current options:
% 11.97/2.00  ------ 
% 11.97/2.00  
% 11.97/2.00  ------ Input Options
% 11.97/2.00  
% 11.97/2.00  --out_options                           all
% 11.97/2.00  --tptp_safe_out                         true
% 11.97/2.00  --problem_path                          ""
% 11.97/2.00  --include_path                          ""
% 11.97/2.00  --clausifier                            res/vclausify_rel
% 11.97/2.00  --clausifier_options                    --mode clausify
% 11.97/2.00  --stdin                                 false
% 11.97/2.00  --stats_out                             all
% 11.97/2.00  
% 11.97/2.00  ------ General Options
% 11.97/2.00  
% 11.97/2.00  --fof                                   false
% 11.97/2.00  --time_out_real                         305.
% 11.97/2.00  --time_out_virtual                      -1.
% 11.97/2.00  --symbol_type_check                     false
% 11.97/2.00  --clausify_out                          false
% 11.97/2.00  --sig_cnt_out                           false
% 11.97/2.00  --trig_cnt_out                          false
% 11.97/2.00  --trig_cnt_out_tolerance                1.
% 11.97/2.00  --trig_cnt_out_sk_spl                   false
% 11.97/2.00  --abstr_cl_out                          false
% 11.97/2.00  
% 11.97/2.00  ------ Global Options
% 11.97/2.00  
% 11.97/2.00  --schedule                              default
% 11.97/2.00  --add_important_lit                     false
% 11.97/2.00  --prop_solver_per_cl                    1000
% 11.97/2.00  --min_unsat_core                        false
% 11.97/2.00  --soft_assumptions                      false
% 11.97/2.00  --soft_lemma_size                       3
% 11.97/2.00  --prop_impl_unit_size                   0
% 11.97/2.00  --prop_impl_unit                        []
% 11.97/2.00  --share_sel_clauses                     true
% 11.97/2.00  --reset_solvers                         false
% 11.97/2.00  --bc_imp_inh                            [conj_cone]
% 11.97/2.00  --conj_cone_tolerance                   3.
% 11.97/2.00  --extra_neg_conj                        none
% 11.97/2.00  --large_theory_mode                     true
% 11.97/2.00  --prolific_symb_bound                   200
% 11.97/2.00  --lt_threshold                          2000
% 11.97/2.00  --clause_weak_htbl                      true
% 11.97/2.00  --gc_record_bc_elim                     false
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing Options
% 11.97/2.00  
% 11.97/2.00  --preprocessing_flag                    true
% 11.97/2.00  --time_out_prep_mult                    0.1
% 11.97/2.00  --splitting_mode                        input
% 11.97/2.00  --splitting_grd                         true
% 11.97/2.00  --splitting_cvd                         false
% 11.97/2.00  --splitting_cvd_svl                     false
% 11.97/2.00  --splitting_nvd                         32
% 11.97/2.00  --sub_typing                            true
% 11.97/2.00  --prep_gs_sim                           true
% 11.97/2.00  --prep_unflatten                        true
% 11.97/2.00  --prep_res_sim                          true
% 11.97/2.00  --prep_upred                            true
% 11.97/2.00  --prep_sem_filter                       exhaustive
% 11.97/2.00  --prep_sem_filter_out                   false
% 11.97/2.00  --pred_elim                             true
% 11.97/2.00  --res_sim_input                         true
% 11.97/2.00  --eq_ax_congr_red                       true
% 11.97/2.00  --pure_diseq_elim                       true
% 11.97/2.00  --brand_transform                       false
% 11.97/2.00  --non_eq_to_eq                          false
% 11.97/2.00  --prep_def_merge                        true
% 11.97/2.00  --prep_def_merge_prop_impl              false
% 11.97/2.00  --prep_def_merge_mbd                    true
% 11.97/2.00  --prep_def_merge_tr_red                 false
% 11.97/2.00  --prep_def_merge_tr_cl                  false
% 11.97/2.00  --smt_preprocessing                     true
% 11.97/2.00  --smt_ac_axioms                         fast
% 11.97/2.00  --preprocessed_out                      false
% 11.97/2.00  --preprocessed_stats                    false
% 11.97/2.00  
% 11.97/2.00  ------ Abstraction refinement Options
% 11.97/2.00  
% 11.97/2.00  --abstr_ref                             []
% 11.97/2.00  --abstr_ref_prep                        false
% 11.97/2.00  --abstr_ref_until_sat                   false
% 11.97/2.00  --abstr_ref_sig_restrict                funpre
% 11.97/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.97/2.00  --abstr_ref_under                       []
% 11.97/2.00  
% 11.97/2.00  ------ SAT Options
% 11.97/2.00  
% 11.97/2.00  --sat_mode                              false
% 11.97/2.00  --sat_fm_restart_options                ""
% 11.97/2.00  --sat_gr_def                            false
% 11.97/2.00  --sat_epr_types                         true
% 11.97/2.00  --sat_non_cyclic_types                  false
% 11.97/2.00  --sat_finite_models                     false
% 11.97/2.00  --sat_fm_lemmas                         false
% 11.97/2.00  --sat_fm_prep                           false
% 11.97/2.00  --sat_fm_uc_incr                        true
% 11.97/2.00  --sat_out_model                         small
% 11.97/2.00  --sat_out_clauses                       false
% 11.97/2.00  
% 11.97/2.00  ------ QBF Options
% 11.97/2.00  
% 11.97/2.00  --qbf_mode                              false
% 11.97/2.00  --qbf_elim_univ                         false
% 11.97/2.00  --qbf_dom_inst                          none
% 11.97/2.00  --qbf_dom_pre_inst                      false
% 11.97/2.00  --qbf_sk_in                             false
% 11.97/2.00  --qbf_pred_elim                         true
% 11.97/2.00  --qbf_split                             512
% 11.97/2.00  
% 11.97/2.00  ------ BMC1 Options
% 11.97/2.00  
% 11.97/2.00  --bmc1_incremental                      false
% 11.97/2.00  --bmc1_axioms                           reachable_all
% 11.97/2.00  --bmc1_min_bound                        0
% 11.97/2.00  --bmc1_max_bound                        -1
% 11.97/2.00  --bmc1_max_bound_default                -1
% 11.97/2.00  --bmc1_symbol_reachability              true
% 11.97/2.00  --bmc1_property_lemmas                  false
% 11.97/2.00  --bmc1_k_induction                      false
% 11.97/2.00  --bmc1_non_equiv_states                 false
% 11.97/2.00  --bmc1_deadlock                         false
% 11.97/2.00  --bmc1_ucm                              false
% 11.97/2.00  --bmc1_add_unsat_core                   none
% 11.97/2.00  --bmc1_unsat_core_children              false
% 11.97/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.97/2.00  --bmc1_out_stat                         full
% 11.97/2.00  --bmc1_ground_init                      false
% 11.97/2.00  --bmc1_pre_inst_next_state              false
% 11.97/2.00  --bmc1_pre_inst_state                   false
% 11.97/2.00  --bmc1_pre_inst_reach_state             false
% 11.97/2.00  --bmc1_out_unsat_core                   false
% 11.97/2.00  --bmc1_aig_witness_out                  false
% 11.97/2.00  --bmc1_verbose                          false
% 11.97/2.00  --bmc1_dump_clauses_tptp                false
% 11.97/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.97/2.00  --bmc1_dump_file                        -
% 11.97/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.97/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.97/2.00  --bmc1_ucm_extend_mode                  1
% 11.97/2.00  --bmc1_ucm_init_mode                    2
% 11.97/2.00  --bmc1_ucm_cone_mode                    none
% 11.97/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.97/2.00  --bmc1_ucm_relax_model                  4
% 11.97/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.97/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.97/2.00  --bmc1_ucm_layered_model                none
% 11.97/2.00  --bmc1_ucm_max_lemma_size               10
% 11.97/2.00  
% 11.97/2.00  ------ AIG Options
% 11.97/2.00  
% 11.97/2.00  --aig_mode                              false
% 11.97/2.00  
% 11.97/2.00  ------ Instantiation Options
% 11.97/2.00  
% 11.97/2.00  --instantiation_flag                    true
% 11.97/2.00  --inst_sos_flag                         false
% 11.97/2.00  --inst_sos_phase                        true
% 11.97/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.97/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.97/2.00  --inst_lit_sel_side                     none
% 11.97/2.00  --inst_solver_per_active                1400
% 11.97/2.00  --inst_solver_calls_frac                1.
% 11.97/2.00  --inst_passive_queue_type               priority_queues
% 11.97/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.97/2.00  --inst_passive_queues_freq              [25;2]
% 11.97/2.00  --inst_dismatching                      true
% 11.97/2.00  --inst_eager_unprocessed_to_passive     true
% 11.97/2.00  --inst_prop_sim_given                   true
% 11.97/2.00  --inst_prop_sim_new                     false
% 11.97/2.00  --inst_subs_new                         false
% 11.97/2.00  --inst_eq_res_simp                      false
% 11.97/2.00  --inst_subs_given                       false
% 11.97/2.00  --inst_orphan_elimination               true
% 11.97/2.00  --inst_learning_loop_flag               true
% 11.97/2.00  --inst_learning_start                   3000
% 11.97/2.00  --inst_learning_factor                  2
% 11.97/2.00  --inst_start_prop_sim_after_learn       3
% 11.97/2.00  --inst_sel_renew                        solver
% 11.97/2.00  --inst_lit_activity_flag                true
% 11.97/2.00  --inst_restr_to_given                   false
% 11.97/2.00  --inst_activity_threshold               500
% 11.97/2.00  --inst_out_proof                        true
% 11.97/2.00  
% 11.97/2.00  ------ Resolution Options
% 11.97/2.00  
% 11.97/2.00  --resolution_flag                       false
% 11.97/2.00  --res_lit_sel                           adaptive
% 11.97/2.00  --res_lit_sel_side                      none
% 11.97/2.00  --res_ordering                          kbo
% 11.97/2.00  --res_to_prop_solver                    active
% 11.97/2.00  --res_prop_simpl_new                    false
% 11.97/2.00  --res_prop_simpl_given                  true
% 11.97/2.00  --res_passive_queue_type                priority_queues
% 11.97/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.97/2.00  --res_passive_queues_freq               [15;5]
% 11.97/2.00  --res_forward_subs                      full
% 11.97/2.00  --res_backward_subs                     full
% 11.97/2.00  --res_forward_subs_resolution           true
% 11.97/2.00  --res_backward_subs_resolution          true
% 11.97/2.00  --res_orphan_elimination                true
% 11.97/2.00  --res_time_limit                        2.
% 11.97/2.00  --res_out_proof                         true
% 11.97/2.00  
% 11.97/2.00  ------ Superposition Options
% 11.97/2.00  
% 11.97/2.00  --superposition_flag                    true
% 11.97/2.00  --sup_passive_queue_type                priority_queues
% 11.97/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.97/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.97/2.00  --demod_completeness_check              fast
% 11.97/2.00  --demod_use_ground                      true
% 11.97/2.00  --sup_to_prop_solver                    passive
% 11.97/2.00  --sup_prop_simpl_new                    true
% 11.97/2.00  --sup_prop_simpl_given                  true
% 11.97/2.00  --sup_fun_splitting                     false
% 11.97/2.00  --sup_smt_interval                      50000
% 11.97/2.00  
% 11.97/2.00  ------ Superposition Simplification Setup
% 11.97/2.00  
% 11.97/2.00  --sup_indices_passive                   []
% 11.97/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.97/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/2.00  --sup_full_bw                           [BwDemod]
% 11.97/2.00  --sup_immed_triv                        [TrivRules]
% 11.97/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/2.00  --sup_immed_bw_main                     []
% 11.97/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.97/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/2.00  
% 11.97/2.00  ------ Combination Options
% 11.97/2.00  
% 11.97/2.00  --comb_res_mult                         3
% 11.97/2.00  --comb_sup_mult                         2
% 11.97/2.00  --comb_inst_mult                        10
% 11.97/2.00  
% 11.97/2.00  ------ Debug Options
% 11.97/2.00  
% 11.97/2.00  --dbg_backtrace                         false
% 11.97/2.00  --dbg_dump_prop_clauses                 false
% 11.97/2.00  --dbg_dump_prop_clauses_file            -
% 11.97/2.00  --dbg_out_stat                          false
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  ------ Proving...
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  % SZS status Theorem for theBenchmark.p
% 11.97/2.00  
% 11.97/2.00   Resolution empty clause
% 11.97/2.00  
% 11.97/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.97/2.00  
% 11.97/2.00  fof(f13,conjecture,(
% 11.97/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f14,negated_conjecture,(
% 11.97/2.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 11.97/2.00    inference(negated_conjecture,[],[f13])).
% 11.97/2.00  
% 11.97/2.00  fof(f29,plain,(
% 11.97/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.97/2.00    inference(ennf_transformation,[],[f14])).
% 11.97/2.00  
% 11.97/2.00  fof(f30,plain,(
% 11.97/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.97/2.00    inference(flattening,[],[f29])).
% 11.97/2.00  
% 11.97/2.00  fof(f37,plain,(
% 11.97/2.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5) & r1_tarski(sK5,u1_struct_0(X2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 11.97/2.00    introduced(choice_axiom,[])).
% 11.97/2.00  
% 11.97/2.00  fof(f36,plain,(
% 11.97/2.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 11.97/2.00    introduced(choice_axiom,[])).
% 11.97/2.00  
% 11.97/2.00  fof(f35,plain,(
% 11.97/2.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 11.97/2.00    introduced(choice_axiom,[])).
% 11.97/2.00  
% 11.97/2.00  fof(f34,plain,(
% 11.97/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 11.97/2.00    introduced(choice_axiom,[])).
% 11.97/2.00  
% 11.97/2.00  fof(f33,plain,(
% 11.97/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 11.97/2.00    introduced(choice_axiom,[])).
% 11.97/2.00  
% 11.97/2.00  fof(f32,plain,(
% 11.97/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 11.97/2.00    introduced(choice_axiom,[])).
% 11.97/2.00  
% 11.97/2.00  fof(f38,plain,(
% 11.97/2.00    (((((k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 11.97/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f37,f36,f35,f34,f33,f32])).
% 11.97/2.00  
% 11.97/2.00  fof(f65,plain,(
% 11.97/2.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f8,axiom,(
% 11.97/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f20,plain,(
% 11.97/2.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.97/2.00    inference(ennf_transformation,[],[f8])).
% 11.97/2.00  
% 11.97/2.00  fof(f47,plain,(
% 11.97/2.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.97/2.00    inference(cnf_transformation,[],[f20])).
% 11.97/2.00  
% 11.97/2.00  fof(f7,axiom,(
% 11.97/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f19,plain,(
% 11.97/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.97/2.00    inference(ennf_transformation,[],[f7])).
% 11.97/2.00  
% 11.97/2.00  fof(f46,plain,(
% 11.97/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.97/2.00    inference(cnf_transformation,[],[f19])).
% 11.97/2.00  
% 11.97/2.00  fof(f1,axiom,(
% 11.97/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f31,plain,(
% 11.97/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.97/2.00    inference(nnf_transformation,[],[f1])).
% 11.97/2.00  
% 11.97/2.00  fof(f39,plain,(
% 11.97/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.97/2.00    inference(cnf_transformation,[],[f31])).
% 11.97/2.00  
% 11.97/2.00  fof(f2,axiom,(
% 11.97/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f15,plain,(
% 11.97/2.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.97/2.00    inference(ennf_transformation,[],[f2])).
% 11.97/2.00  
% 11.97/2.00  fof(f41,plain,(
% 11.97/2.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f15])).
% 11.97/2.00  
% 11.97/2.00  fof(f40,plain,(
% 11.97/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f31])).
% 11.97/2.00  
% 11.97/2.00  fof(f3,axiom,(
% 11.97/2.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f42,plain,(
% 11.97/2.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.97/2.00    inference(cnf_transformation,[],[f3])).
% 11.97/2.00  
% 11.97/2.00  fof(f4,axiom,(
% 11.97/2.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f16,plain,(
% 11.97/2.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.97/2.00    inference(ennf_transformation,[],[f4])).
% 11.97/2.00  
% 11.97/2.00  fof(f43,plain,(
% 11.97/2.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f16])).
% 11.97/2.00  
% 11.97/2.00  fof(f6,axiom,(
% 11.97/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f18,plain,(
% 11.97/2.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 11.97/2.00    inference(ennf_transformation,[],[f6])).
% 11.97/2.00  
% 11.97/2.00  fof(f45,plain,(
% 11.97/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f18])).
% 11.97/2.00  
% 11.97/2.00  fof(f9,axiom,(
% 11.97/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f21,plain,(
% 11.97/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 11.97/2.00    inference(ennf_transformation,[],[f9])).
% 11.97/2.00  
% 11.97/2.00  fof(f22,plain,(
% 11.97/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 11.97/2.00    inference(flattening,[],[f21])).
% 11.97/2.00  
% 11.97/2.00  fof(f48,plain,(
% 11.97/2.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f22])).
% 11.97/2.00  
% 11.97/2.00  fof(f11,axiom,(
% 11.97/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f25,plain,(
% 11.97/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.97/2.00    inference(ennf_transformation,[],[f11])).
% 11.97/2.00  
% 11.97/2.00  fof(f26,plain,(
% 11.97/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.97/2.00    inference(flattening,[],[f25])).
% 11.97/2.00  
% 11.97/2.00  fof(f51,plain,(
% 11.97/2.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f26])).
% 11.97/2.00  
% 11.97/2.00  fof(f63,plain,(
% 11.97/2.00    v1_funct_1(sK4)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f10,axiom,(
% 11.97/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f23,plain,(
% 11.97/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.97/2.00    inference(ennf_transformation,[],[f10])).
% 11.97/2.00  
% 11.97/2.00  fof(f24,plain,(
% 11.97/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.97/2.00    inference(flattening,[],[f23])).
% 11.97/2.00  
% 11.97/2.00  fof(f50,plain,(
% 11.97/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f24])).
% 11.97/2.00  
% 11.97/2.00  fof(f60,plain,(
% 11.97/2.00    m1_pre_topc(sK2,sK0)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f12,axiom,(
% 11.97/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f27,plain,(
% 11.97/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.97/2.00    inference(ennf_transformation,[],[f12])).
% 11.97/2.00  
% 11.97/2.00  fof(f28,plain,(
% 11.97/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.97/2.00    inference(flattening,[],[f27])).
% 11.97/2.00  
% 11.97/2.00  fof(f52,plain,(
% 11.97/2.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f28])).
% 11.97/2.00  
% 11.97/2.00  fof(f64,plain,(
% 11.97/2.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f56,plain,(
% 11.97/2.00    ~v2_struct_0(sK1)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f57,plain,(
% 11.97/2.00    v2_pre_topc(sK1)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f58,plain,(
% 11.97/2.00    l1_pre_topc(sK1)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f53,plain,(
% 11.97/2.00    ~v2_struct_0(sK0)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f54,plain,(
% 11.97/2.00    v2_pre_topc(sK0)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f55,plain,(
% 11.97/2.00    l1_pre_topc(sK0)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f62,plain,(
% 11.97/2.00    m1_pre_topc(sK3,sK0)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f66,plain,(
% 11.97/2.00    m1_pre_topc(sK2,sK3)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f69,plain,(
% 11.97/2.00    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f68,plain,(
% 11.97/2.00    r1_tarski(sK5,u1_struct_0(sK2))),
% 11.97/2.00    inference(cnf_transformation,[],[f38])).
% 11.97/2.00  
% 11.97/2.00  fof(f5,axiom,(
% 11.97/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 11.97/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.97/2.00  
% 11.97/2.00  fof(f17,plain,(
% 11.97/2.00    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 11.97/2.00    inference(ennf_transformation,[],[f5])).
% 11.97/2.00  
% 11.97/2.00  fof(f44,plain,(
% 11.97/2.00    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 11.97/2.00    inference(cnf_transformation,[],[f17])).
% 11.97/2.00  
% 11.97/2.00  cnf(c_18,negated_conjecture,
% 11.97/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 11.97/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_704,negated_conjecture,
% 11.97/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_18]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1428,plain,
% 11.97/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_8,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.97/2.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 11.97/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_713,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.97/2.00      | k7_relset_1(X1_54,X2_54,X0_54,X3_54) = k9_relat_1(X0_54,X3_54) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_8]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1420,plain,
% 11.97/2.00      ( k7_relset_1(X0_54,X1_54,X2_54,X3_54) = k9_relat_1(X2_54,X3_54)
% 11.97/2.00      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2448,plain,
% 11.97/2.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k9_relat_1(sK4,X0_54) ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_1428,c_1420]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_7,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.97/2.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 11.97/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_714,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.97/2.00      | m1_subset_1(k7_relset_1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(X2_54)) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_7]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1419,plain,
% 11.97/2.00      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 11.97/2.00      | m1_subset_1(k7_relset_1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(X2_54)) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2803,plain,
% 11.97/2.00      ( m1_subset_1(k9_relat_1(sK4,X0_54),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 11.97/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_2448,c_1419]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_43,plain,
% 11.97/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_4129,plain,
% 11.97/2.00      ( m1_subset_1(k9_relat_1(sK4,X0_54),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.97/2.00      inference(global_propositional_subsumption,[status(thm)],[c_2803,c_43]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1,plain,
% 11.97/2.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.97/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_719,plain,
% 11.97/2.00      ( r1_tarski(X0_54,X1_54) | ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_1]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1414,plain,
% 11.97/2.00      ( r1_tarski(X0_54,X1_54) = iProver_top
% 11.97/2.00      | m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_4136,plain,
% 11.97/2.00      ( r1_tarski(k9_relat_1(sK4,X0_54),u1_struct_0(sK1)) = iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_4129,c_1414]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2316,plain,
% 11.97/2.00      ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) = iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_1428,c_1414]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_0,plain,
% 11.97/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.97/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_215,plain,
% 11.97/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.97/2.00      inference(prop_impl,[status(thm)],[c_0]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_270,plain,
% 11.97/2.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.97/2.00      inference(bin_hyper_res,[status(thm)],[c_2,c_215]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_692,plain,
% 11.97/2.00      ( ~ r1_tarski(X0_54,X1_54) | ~ v1_relat_1(X1_54) | v1_relat_1(X0_54) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_270]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1440,plain,
% 11.97/2.00      ( r1_tarski(X0_54,X1_54) != iProver_top
% 11.97/2.00      | v1_relat_1(X1_54) != iProver_top
% 11.97/2.00      | v1_relat_1(X0_54) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_3732,plain,
% 11.97/2.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
% 11.97/2.00      | v1_relat_1(sK4) = iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_2316,c_1440]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1650,plain,
% 11.97/2.00      ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
% 11.97/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_719]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1651,plain,
% 11.97/2.00      ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) = iProver_top
% 11.97/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_1650]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1637,plain,
% 11.97/2.00      ( ~ r1_tarski(X0_54,k2_zfmisc_1(X1_54,X2_54))
% 11.97/2.00      | v1_relat_1(X0_54)
% 11.97/2.00      | ~ v1_relat_1(k2_zfmisc_1(X1_54,X2_54)) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_692]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2093,plain,
% 11.97/2.00      ( ~ r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
% 11.97/2.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
% 11.97/2.00      | v1_relat_1(sK4) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_1637]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2094,plain,
% 11.97/2.00      ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
% 11.97/2.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
% 11.97/2.00      | v1_relat_1(sK4) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_2093]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_3,plain,
% 11.97/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.97/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_718,plain,
% 11.97/2.00      ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_3]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2256,plain,
% 11.97/2.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_718]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2257,plain,
% 11.97/2.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_2256]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_3927,plain,
% 11.97/2.00      ( v1_relat_1(sK4) = iProver_top ),
% 11.97/2.00      inference(global_propositional_subsumption,
% 11.97/2.00                [status(thm)],
% 11.97/2.00                [c_3732,c_43,c_1651,c_2094,c_2257]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_4,plain,
% 11.97/2.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.97/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_717,plain,
% 11.97/2.00      ( ~ v1_relat_1(X0_54)
% 11.97/2.00      | k2_relat_1(k7_relat_1(X0_54,X1_54)) = k9_relat_1(X0_54,X1_54) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_4]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1416,plain,
% 11.97/2.00      ( k2_relat_1(k7_relat_1(X0_54,X1_54)) = k9_relat_1(X0_54,X1_54)
% 11.97/2.00      | v1_relat_1(X0_54) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_3934,plain,
% 11.97/2.00      ( k2_relat_1(k7_relat_1(sK4,X0_54)) = k9_relat_1(sK4,X0_54) ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_3927,c_1416]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_6,plain,
% 11.97/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_715,plain,
% 11.97/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X1_54)),X1_54)
% 11.97/2.00      | ~ v1_relat_1(X0_54) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_6]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1418,plain,
% 11.97/2.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X1_54)),X1_54) = iProver_top
% 11.97/2.00      | v1_relat_1(X0_54) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_9,plain,
% 11.97/2.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 11.97/2.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 11.97/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.97/2.00      | ~ v1_relat_1(X0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_712,plain,
% 11.97/2.00      ( ~ r1_tarski(k1_relat_1(X0_54),X1_54)
% 11.97/2.00      | ~ r1_tarski(k2_relat_1(X0_54),X2_54)
% 11.97/2.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.97/2.00      | ~ v1_relat_1(X0_54) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_9]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1421,plain,
% 11.97/2.00      ( r1_tarski(k1_relat_1(X0_54),X1_54) != iProver_top
% 11.97/2.00      | r1_tarski(k2_relat_1(X0_54),X2_54) != iProver_top
% 11.97/2.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) = iProver_top
% 11.97/2.00      | v1_relat_1(X0_54) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_3522,plain,
% 11.97/2.00      ( k7_relset_1(X0_54,X1_54,X2_54,X3_54) = k9_relat_1(X2_54,X3_54)
% 11.97/2.00      | r1_tarski(k1_relat_1(X2_54),X0_54) != iProver_top
% 11.97/2.00      | r1_tarski(k2_relat_1(X2_54),X1_54) != iProver_top
% 11.97/2.00      | v1_relat_1(X2_54) != iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_1421,c_1420]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_16116,plain,
% 11.97/2.00      ( k7_relset_1(X0_54,X1_54,k7_relat_1(X2_54,X0_54),X3_54) = k9_relat_1(k7_relat_1(X2_54,X0_54),X3_54)
% 11.97/2.00      | r1_tarski(k2_relat_1(k7_relat_1(X2_54,X0_54)),X1_54) != iProver_top
% 11.97/2.00      | v1_relat_1(X2_54) != iProver_top
% 11.97/2.00      | v1_relat_1(k7_relat_1(X2_54,X0_54)) != iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_1418,c_3522]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_38819,plain,
% 11.97/2.00      ( k7_relset_1(X0_54,X1_54,k7_relat_1(sK4,X0_54),X2_54) = k9_relat_1(k7_relat_1(sK4,X0_54),X2_54)
% 11.97/2.00      | r1_tarski(k9_relat_1(sK4,X0_54),X1_54) != iProver_top
% 11.97/2.00      | v1_relat_1(k7_relat_1(sK4,X0_54)) != iProver_top
% 11.97/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_3934,c_16116]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_12,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.97/2.00      | ~ v1_funct_1(X0)
% 11.97/2.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.97/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_709,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.97/2.00      | ~ v1_funct_1(X0_54)
% 11.97/2.00      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_12]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1424,plain,
% 11.97/2.00      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 11.97/2.00      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 11.97/2.00      | v1_funct_1(X2_54) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2933,plain,
% 11.97/2.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54)
% 11.97/2.00      | v1_funct_1(sK4) != iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_1428,c_1424]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_20,negated_conjecture,
% 11.97/2.00      ( v1_funct_1(sK4) ),
% 11.97/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1717,plain,
% 11.97/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.97/2.00      | ~ v1_funct_1(sK4)
% 11.97/2.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 11.97/2.00      inference(instantiation,[status(thm)],[c_709]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_3174,plain,
% 11.97/2.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 11.97/2.00      inference(global_propositional_subsumption,
% 11.97/2.00                [status(thm)],
% 11.97/2.00                [c_2933,c_20,c_18,c_1717]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_10,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.97/2.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.97/2.00      | ~ v1_funct_1(X0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_711,plain,
% 11.97/2.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.97/2.00      | m1_subset_1(k2_partfun1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.97/2.00      | ~ v1_funct_1(X0_54) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_10]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1422,plain,
% 11.97/2.00      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 11.97/2.00      | m1_subset_1(k2_partfun1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) = iProver_top
% 11.97/2.00      | v1_funct_1(X0_54) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_3211,plain,
% 11.97/2.00      ( m1_subset_1(k7_relat_1(sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 11.97/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.97/2.00      | v1_funct_1(sK4) != iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_3174,c_1422]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_41,plain,
% 11.97/2.00      ( v1_funct_1(sK4) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_4210,plain,
% 11.97/2.00      ( m1_subset_1(k7_relat_1(sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 11.97/2.00      inference(global_propositional_subsumption,
% 11.97/2.00                [status(thm)],
% 11.97/2.00                [c_3211,c_41,c_43]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_4218,plain,
% 11.97/2.00      ( r1_tarski(k7_relat_1(sK4,X0_54),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) = iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_4210,c_1414]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_4468,plain,
% 11.97/2.00      ( v1_relat_1(k7_relat_1(sK4,X0_54)) = iProver_top
% 11.97/2.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_4218,c_1440]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_47422,plain,
% 11.97/2.00      ( k7_relset_1(X0_54,X1_54,k7_relat_1(sK4,X0_54),X2_54) = k9_relat_1(k7_relat_1(sK4,X0_54),X2_54)
% 11.97/2.00      | r1_tarski(k9_relat_1(sK4,X0_54),X1_54) != iProver_top ),
% 11.97/2.00      inference(global_propositional_subsumption,
% 11.97/2.00                [status(thm)],
% 11.97/2.00                [c_38819,c_43,c_1651,c_2094,c_2257,c_4468]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_47431,plain,
% 11.97/2.00      ( k7_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK4,X0_54),X1_54) = k9_relat_1(k7_relat_1(sK4,X0_54),X1_54) ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_4136,c_47422]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_23,negated_conjecture,
% 11.97/2.00      ( m1_pre_topc(sK2,sK0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_700,negated_conjecture,
% 11.97/2.00      ( m1_pre_topc(sK2,sK0) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_23]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1432,plain,
% 11.97/2.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_13,plain,
% 11.97/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.97/2.00      | ~ m1_pre_topc(X3,X1)
% 11.97/2.00      | ~ m1_pre_topc(X3,X4)
% 11.97/2.00      | ~ m1_pre_topc(X1,X4)
% 11.97/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.97/2.00      | v2_struct_0(X4)
% 11.97/2.00      | v2_struct_0(X2)
% 11.97/2.00      | ~ v2_pre_topc(X2)
% 11.97/2.00      | ~ v2_pre_topc(X4)
% 11.97/2.00      | ~ l1_pre_topc(X2)
% 11.97/2.00      | ~ l1_pre_topc(X4)
% 11.97/2.00      | ~ v1_funct_1(X0)
% 11.97/2.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_19,negated_conjecture,
% 11.97/2.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 11.97/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_382,plain,
% 11.97/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.97/2.00      | ~ m1_pre_topc(X0,X2)
% 11.97/2.00      | ~ m1_pre_topc(X1,X2)
% 11.97/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 11.97/2.00      | v2_struct_0(X2)
% 11.97/2.00      | v2_struct_0(X4)
% 11.97/2.00      | ~ v2_pre_topc(X4)
% 11.97/2.00      | ~ v2_pre_topc(X2)
% 11.97/2.00      | ~ l1_pre_topc(X4)
% 11.97/2.00      | ~ l1_pre_topc(X2)
% 11.97/2.00      | ~ v1_funct_1(X3)
% 11.97/2.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 11.97/2.00      | u1_struct_0(X4) != u1_struct_0(sK1)
% 11.97/2.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 11.97/2.00      | sK4 != X3 ),
% 11.97/2.00      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_383,plain,
% 11.97/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.97/2.00      | ~ m1_pre_topc(X0,X2)
% 11.97/2.00      | ~ m1_pre_topc(X1,X2)
% 11.97/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 11.97/2.00      | v2_struct_0(X3)
% 11.97/2.00      | v2_struct_0(X2)
% 11.97/2.00      | ~ v2_pre_topc(X2)
% 11.97/2.00      | ~ v2_pre_topc(X3)
% 11.97/2.00      | ~ l1_pre_topc(X2)
% 11.97/2.00      | ~ l1_pre_topc(X3)
% 11.97/2.00      | ~ v1_funct_1(sK4)
% 11.97/2.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 11.97/2.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 11.97/2.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 11.97/2.00      inference(unflattening,[status(thm)],[c_382]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_387,plain,
% 11.97/2.00      ( ~ l1_pre_topc(X3)
% 11.97/2.00      | ~ l1_pre_topc(X2)
% 11.97/2.00      | ~ v2_pre_topc(X3)
% 11.97/2.00      | ~ v2_pre_topc(X2)
% 11.97/2.00      | v2_struct_0(X2)
% 11.97/2.00      | v2_struct_0(X3)
% 11.97/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 11.97/2.00      | ~ m1_pre_topc(X1,X2)
% 11.97/2.00      | ~ m1_pre_topc(X0,X2)
% 11.97/2.00      | ~ m1_pre_topc(X0,X1)
% 11.97/2.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 11.97/2.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 11.97/2.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 11.97/2.00      inference(global_propositional_subsumption,[status(thm)],[c_383,c_20]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_388,plain,
% 11.97/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.97/2.00      | ~ m1_pre_topc(X0,X2)
% 11.97/2.00      | ~ m1_pre_topc(X1,X2)
% 11.97/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 11.97/2.00      | v2_struct_0(X2)
% 11.97/2.00      | v2_struct_0(X3)
% 11.97/2.00      | ~ v2_pre_topc(X2)
% 11.97/2.00      | ~ v2_pre_topc(X3)
% 11.97/2.00      | ~ l1_pre_topc(X2)
% 11.97/2.00      | ~ l1_pre_topc(X3)
% 11.97/2.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 11.97/2.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 11.97/2.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 11.97/2.00      inference(renaming,[status(thm)],[c_387]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_691,plain,
% 11.97/2.00      ( ~ m1_pre_topc(X0_53,X1_53)
% 11.97/2.00      | ~ m1_pre_topc(X0_53,X2_53)
% 11.97/2.00      | ~ m1_pre_topc(X1_53,X2_53)
% 11.97/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X3_53))))
% 11.97/2.00      | v2_struct_0(X2_53)
% 11.97/2.00      | v2_struct_0(X3_53)
% 11.97/2.00      | ~ v2_pre_topc(X2_53)
% 11.97/2.00      | ~ v2_pre_topc(X3_53)
% 11.97/2.00      | ~ l1_pre_topc(X2_53)
% 11.97/2.00      | ~ l1_pre_topc(X3_53)
% 11.97/2.00      | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X3_53),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X2_53,X3_53,X1_53,X0_53,sK4)
% 11.97/2.00      | u1_struct_0(X3_53) != u1_struct_0(sK1)
% 11.97/2.00      | u1_struct_0(X1_53) != u1_struct_0(sK3) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_388]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1441,plain,
% 11.97/2.00      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK4,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK4)
% 11.97/2.00      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 11.97/2.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 11.97/2.00      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 11.97/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 11.97/2.00      | v2_struct_0(X1_53) = iProver_top
% 11.97/2.00      | v2_struct_0(X3_53) = iProver_top
% 11.97/2.00      | v2_pre_topc(X1_53) != iProver_top
% 11.97/2.00      | v2_pre_topc(X3_53) != iProver_top
% 11.97/2.00      | l1_pre_topc(X1_53) != iProver_top
% 11.97/2.00      | l1_pre_topc(X3_53) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2089,plain,
% 11.97/2.00      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
% 11.97/2.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 11.97/2.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 11.97/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 11.97/2.00      | v2_struct_0(X2_53) = iProver_top
% 11.97/2.00      | v2_struct_0(sK1) = iProver_top
% 11.97/2.00      | v2_pre_topc(X2_53) != iProver_top
% 11.97/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.97/2.00      | l1_pre_topc(X2_53) != iProver_top
% 11.97/2.00      | l1_pre_topc(sK1) != iProver_top ),
% 11.97/2.00      inference(equality_resolution,[status(thm)],[c_1441]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_27,negated_conjecture,
% 11.97/2.00      ( ~ v2_struct_0(sK1) ),
% 11.97/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_34,plain,
% 11.97/2.00      ( v2_struct_0(sK1) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_26,negated_conjecture,
% 11.97/2.00      ( v2_pre_topc(sK1) ),
% 11.97/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_35,plain,
% 11.97/2.00      ( v2_pre_topc(sK1) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_25,negated_conjecture,
% 11.97/2.00      ( l1_pre_topc(sK1) ),
% 11.97/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_36,plain,
% 11.97/2.00      ( l1_pre_topc(sK1) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2183,plain,
% 11.97/2.00      ( l1_pre_topc(X2_53) != iProver_top
% 11.97/2.00      | v2_struct_0(X2_53) = iProver_top
% 11.97/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 11.97/2.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 11.97/2.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 11.97/2.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
% 11.97/2.00      | v2_pre_topc(X2_53) != iProver_top ),
% 11.97/2.00      inference(global_propositional_subsumption,
% 11.97/2.00                [status(thm)],
% 11.97/2.00                [c_2089,c_34,c_35,c_36]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2184,plain,
% 11.97/2.00      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK4,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK4)
% 11.97/2.00      | u1_struct_0(X0_53) != u1_struct_0(sK3)
% 11.97/2.00      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 11.97/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 11.97/2.00      | v2_struct_0(X2_53) = iProver_top
% 11.97/2.00      | v2_pre_topc(X2_53) != iProver_top
% 11.97/2.00      | l1_pre_topc(X2_53) != iProver_top ),
% 11.97/2.00      inference(renaming,[status(thm)],[c_2183]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2196,plain,
% 11.97/2.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
% 11.97/2.00      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 11.97/2.00      | m1_pre_topc(sK3,X1_53) != iProver_top
% 11.97/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.97/2.00      | v2_struct_0(X1_53) = iProver_top
% 11.97/2.00      | v2_pre_topc(X1_53) != iProver_top
% 11.97/2.00      | l1_pre_topc(X1_53) != iProver_top ),
% 11.97/2.00      inference(equality_resolution,[status(thm)],[c_2184]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2201,plain,
% 11.97/2.00      ( m1_pre_topc(sK3,X1_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 11.97/2.00      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 11.97/2.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
% 11.97/2.00      | v2_struct_0(X1_53) = iProver_top
% 11.97/2.00      | v2_pre_topc(X1_53) != iProver_top
% 11.97/2.00      | l1_pre_topc(X1_53) != iProver_top ),
% 11.97/2.00      inference(global_propositional_subsumption,[status(thm)],[c_2196,c_43]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2202,plain,
% 11.97/2.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
% 11.97/2.00      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 11.97/2.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 11.97/2.00      | m1_pre_topc(sK3,X1_53) != iProver_top
% 11.97/2.00      | v2_struct_0(X1_53) = iProver_top
% 11.97/2.00      | v2_pre_topc(X1_53) != iProver_top
% 11.97/2.00      | l1_pre_topc(X1_53) != iProver_top ),
% 11.97/2.00      inference(renaming,[status(thm)],[c_2201]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2216,plain,
% 11.97/2.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
% 11.97/2.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.97/2.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.97/2.00      | v2_struct_0(sK0) = iProver_top
% 11.97/2.00      | v2_pre_topc(sK0) != iProver_top
% 11.97/2.00      | l1_pre_topc(sK0) != iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_1432,c_2202]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_30,negated_conjecture,
% 11.97/2.00      ( ~ v2_struct_0(sK0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_31,plain,
% 11.97/2.00      ( v2_struct_0(sK0) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_29,negated_conjecture,
% 11.97/2.00      ( v2_pre_topc(sK0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_32,plain,
% 11.97/2.00      ( v2_pre_topc(sK0) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_28,negated_conjecture,
% 11.97/2.00      ( l1_pre_topc(sK0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_33,plain,
% 11.97/2.00      ( l1_pre_topc(sK0) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_21,negated_conjecture,
% 11.97/2.00      ( m1_pre_topc(sK3,sK0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_40,plain,
% 11.97/2.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_17,negated_conjecture,
% 11.97/2.00      ( m1_pre_topc(sK2,sK3) ),
% 11.97/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_44,plain,
% 11.97/2.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2649,plain,
% 11.97/2.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
% 11.97/2.00      inference(global_propositional_subsumption,
% 11.97/2.00                [status(thm)],
% 11.97/2.00                [c_2216,c_31,c_32,c_33,c_40,c_44]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_3180,plain,
% 11.97/2.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 11.97/2.00      inference(demodulation,[status(thm)],[c_3174,c_2649]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_14,negated_conjecture,
% 11.97/2.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 11.97/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_708,negated_conjecture,
% 11.97/2.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_14]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2588,plain,
% 11.97/2.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
% 11.97/2.00      inference(demodulation,[status(thm)],[c_2448,c_708]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_3431,plain,
% 11.97/2.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
% 11.97/2.00      inference(demodulation,[status(thm)],[c_3180,c_2588]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_47447,plain,
% 11.97/2.00      ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
% 11.97/2.00      inference(demodulation,[status(thm)],[c_47431,c_3431]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_15,negated_conjecture,
% 11.97/2.00      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 11.97/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_707,negated_conjecture,
% 11.97/2.00      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_15]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1425,plain,
% 11.97/2.00      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_5,plain,
% 11.97/2.00      ( ~ r1_tarski(X0,X1)
% 11.97/2.00      | ~ v1_relat_1(X2)
% 11.97/2.00      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 11.97/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_716,plain,
% 11.97/2.00      ( ~ r1_tarski(X0_54,X1_54)
% 11.97/2.00      | ~ v1_relat_1(X2_54)
% 11.97/2.00      | k9_relat_1(k7_relat_1(X2_54,X1_54),X0_54) = k9_relat_1(X2_54,X0_54) ),
% 11.97/2.00      inference(subtyping,[status(esa)],[c_5]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_1417,plain,
% 11.97/2.00      ( k9_relat_1(k7_relat_1(X0_54,X1_54),X2_54) = k9_relat_1(X0_54,X2_54)
% 11.97/2.00      | r1_tarski(X2_54,X1_54) != iProver_top
% 11.97/2.00      | v1_relat_1(X0_54) != iProver_top ),
% 11.97/2.00      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_2766,plain,
% 11.97/2.00      ( k9_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_54,sK5)
% 11.97/2.00      | v1_relat_1(X0_54) != iProver_top ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_1425,c_1417]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_3933,plain,
% 11.97/2.00      ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k9_relat_1(sK4,sK5) ),
% 11.97/2.00      inference(superposition,[status(thm)],[c_3927,c_2766]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_47448,plain,
% 11.97/2.00      ( k9_relat_1(sK4,sK5) != k9_relat_1(sK4,sK5) ),
% 11.97/2.00      inference(light_normalisation,[status(thm)],[c_47447,c_3933]) ).
% 11.97/2.00  
% 11.97/2.00  cnf(c_47449,plain,
% 11.97/2.00      ( $false ),
% 11.97/2.00      inference(equality_resolution_simp,[status(thm)],[c_47448]) ).
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.97/2.00  
% 11.97/2.00  ------                               Statistics
% 11.97/2.00  
% 11.97/2.00  ------ General
% 11.97/2.00  
% 11.97/2.00  abstr_ref_over_cycles:                  0
% 11.97/2.00  abstr_ref_under_cycles:                 0
% 11.97/2.00  gc_basic_clause_elim:                   0
% 11.97/2.00  forced_gc_time:                         0
% 11.97/2.00  parsing_time:                           0.012
% 11.97/2.00  unif_index_cands_time:                  0.
% 11.97/2.00  unif_index_add_time:                    0.
% 11.97/2.00  orderings_time:                         0.
% 11.97/2.00  out_proof_time:                         0.016
% 11.97/2.00  total_time:                             1.411
% 11.97/2.00  num_of_symbols:                         59
% 11.97/2.00  num_of_terms:                           43082
% 11.97/2.00  
% 11.97/2.00  ------ Preprocessing
% 11.97/2.00  
% 11.97/2.00  num_of_splits:                          0
% 11.97/2.00  num_of_split_atoms:                     0
% 11.97/2.00  num_of_reused_defs:                     0
% 11.97/2.00  num_eq_ax_congr_red:                    20
% 11.97/2.00  num_of_sem_filtered_clauses:            1
% 11.97/2.00  num_of_subtypes:                        3
% 11.97/2.00  monotx_restored_types:                  0
% 11.97/2.00  sat_num_of_epr_types:                   0
% 11.97/2.00  sat_num_of_non_cyclic_types:            0
% 11.97/2.00  sat_guarded_non_collapsed_types:        0
% 11.97/2.00  num_pure_diseq_elim:                    0
% 11.97/2.00  simp_replaced_by:                       0
% 11.97/2.00  res_preprocessed:                       152
% 11.97/2.00  prep_upred:                             0
% 11.97/2.00  prep_unflattend:                        1
% 11.97/2.00  smt_new_axioms:                         0
% 11.97/2.00  pred_elim_cands:                        8
% 11.97/2.00  pred_elim:                              1
% 11.97/2.00  pred_elim_cl:                           1
% 11.97/2.00  pred_elim_cycles:                       3
% 11.97/2.00  merged_defs:                            8
% 11.97/2.00  merged_defs_ncl:                        0
% 11.97/2.00  bin_hyper_res:                          9
% 11.97/2.00  prep_cycles:                            4
% 11.97/2.00  pred_elim_time:                         0.002
% 11.97/2.00  splitting_time:                         0.
% 11.97/2.00  sem_filter_time:                        0.
% 11.97/2.00  monotx_time:                            0.
% 11.97/2.00  subtype_inf_time:                       0.
% 11.97/2.00  
% 11.97/2.00  ------ Problem properties
% 11.97/2.00  
% 11.97/2.00  clauses:                                30
% 11.97/2.00  conjectures:                            16
% 11.97/2.00  epr:                                    13
% 11.97/2.00  horn:                                   29
% 11.97/2.00  ground:                                 16
% 11.97/2.00  unary:                                  17
% 11.97/2.00  binary:                                 6
% 11.97/2.00  lits:                                   61
% 11.97/2.00  lits_eq:                                8
% 11.97/2.00  fd_pure:                                0
% 11.97/2.00  fd_pseudo:                              0
% 11.97/2.00  fd_cond:                                0
% 11.97/2.00  fd_pseudo_cond:                         0
% 11.97/2.00  ac_symbols:                             0
% 11.97/2.00  
% 11.97/2.00  ------ Propositional Solver
% 11.97/2.00  
% 11.97/2.00  prop_solver_calls:                      32
% 11.97/2.00  prop_fast_solver_calls:                 1558
% 11.97/2.00  smt_solver_calls:                       0
% 11.97/2.00  smt_fast_solver_calls:                  0
% 11.97/2.00  prop_num_of_clauses:                    13676
% 11.97/2.00  prop_preprocess_simplified:             26019
% 11.97/2.00  prop_fo_subsumed:                       47
% 11.97/2.00  prop_solver_time:                       0.
% 11.97/2.00  smt_solver_time:                        0.
% 11.97/2.00  smt_fast_solver_time:                   0.
% 11.97/2.00  prop_fast_solver_time:                  0.
% 11.97/2.00  prop_unsat_core_time:                   0.
% 11.97/2.00  
% 11.97/2.00  ------ QBF
% 11.97/2.00  
% 11.97/2.00  qbf_q_res:                              0
% 11.97/2.00  qbf_num_tautologies:                    0
% 11.97/2.00  qbf_prep_cycles:                        0
% 11.97/2.00  
% 11.97/2.00  ------ BMC1
% 11.97/2.00  
% 11.97/2.00  bmc1_current_bound:                     -1
% 11.97/2.00  bmc1_last_solved_bound:                 -1
% 11.97/2.00  bmc1_unsat_core_size:                   -1
% 11.97/2.00  bmc1_unsat_core_parents_size:           -1
% 11.97/2.00  bmc1_merge_next_fun:                    0
% 11.97/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.97/2.00  
% 11.97/2.00  ------ Instantiation
% 11.97/2.00  
% 11.97/2.00  inst_num_of_clauses:                    4659
% 11.97/2.00  inst_num_in_passive:                    1129
% 11.97/2.00  inst_num_in_active:                     1995
% 11.97/2.00  inst_num_in_unprocessed:                1535
% 11.97/2.00  inst_num_of_loops:                      2070
% 11.97/2.00  inst_num_of_learning_restarts:          0
% 11.97/2.00  inst_num_moves_active_passive:          70
% 11.97/2.00  inst_lit_activity:                      0
% 11.97/2.00  inst_lit_activity_moves:                0
% 11.97/2.00  inst_num_tautologies:                   0
% 11.97/2.00  inst_num_prop_implied:                  0
% 11.97/2.00  inst_num_existing_simplified:           0
% 11.97/2.00  inst_num_eq_res_simplified:             0
% 11.97/2.00  inst_num_child_elim:                    0
% 11.97/2.00  inst_num_of_dismatching_blockings:      5963
% 11.97/2.00  inst_num_of_non_proper_insts:           7286
% 11.97/2.00  inst_num_of_duplicates:                 0
% 11.97/2.00  inst_inst_num_from_inst_to_res:         0
% 11.97/2.00  inst_dismatching_checking_time:         0.
% 11.97/2.00  
% 11.97/2.00  ------ Resolution
% 11.97/2.00  
% 11.97/2.00  res_num_of_clauses:                     0
% 11.97/2.00  res_num_in_passive:                     0
% 11.97/2.00  res_num_in_active:                      0
% 11.97/2.00  res_num_of_loops:                       156
% 11.97/2.00  res_forward_subset_subsumed:            1054
% 11.97/2.00  res_backward_subset_subsumed:           4
% 11.97/2.00  res_forward_subsumed:                   0
% 11.97/2.00  res_backward_subsumed:                  0
% 11.97/2.00  res_forward_subsumption_resolution:     0
% 11.97/2.00  res_backward_subsumption_resolution:    0
% 11.97/2.00  res_clause_to_clause_subsumption:       5010
% 11.97/2.00  res_orphan_elimination:                 0
% 11.97/2.00  res_tautology_del:                      1247
% 11.97/2.00  res_num_eq_res_simplified:              0
% 11.97/2.00  res_num_sel_changes:                    0
% 11.97/2.00  res_moves_from_active_to_pass:          0
% 11.97/2.00  
% 11.97/2.00  ------ Superposition
% 11.97/2.00  
% 11.97/2.00  sup_time_total:                         0.
% 11.97/2.00  sup_time_generating:                    0.
% 11.97/2.00  sup_time_sim_full:                      0.
% 11.97/2.00  sup_time_sim_immed:                     0.
% 11.97/2.00  
% 11.97/2.00  sup_num_of_clauses:                     1187
% 11.97/2.00  sup_num_in_active:                      396
% 11.97/2.00  sup_num_in_passive:                     791
% 11.97/2.00  sup_num_of_loops:                       413
% 11.97/2.00  sup_fw_superposition:                   889
% 11.97/2.00  sup_bw_superposition:                   479
% 11.97/2.00  sup_immediate_simplified:               190
% 11.97/2.00  sup_given_eliminated:                   0
% 11.97/2.00  comparisons_done:                       0
% 11.97/2.00  comparisons_avoided:                    0
% 11.97/2.00  
% 11.97/2.00  ------ Simplifications
% 11.97/2.00  
% 11.97/2.00  
% 11.97/2.00  sim_fw_subset_subsumed:                 15
% 11.97/2.00  sim_bw_subset_subsumed:                 13
% 11.97/2.00  sim_fw_subsumed:                        80
% 11.97/2.00  sim_bw_subsumed:                        0
% 11.97/2.00  sim_fw_subsumption_res:                 1
% 11.97/2.00  sim_bw_subsumption_res:                 0
% 11.97/2.00  sim_tautology_del:                      2
% 11.97/2.00  sim_eq_tautology_del:                   7
% 11.97/2.00  sim_eq_res_simp:                        0
% 11.97/2.00  sim_fw_demodulated:                     44
% 11.97/2.00  sim_bw_demodulated:                     16
% 11.97/2.00  sim_light_normalised:                   64
% 11.97/2.00  sim_joinable_taut:                      0
% 11.97/2.00  sim_joinable_simp:                      0
% 11.97/2.00  sim_ac_normalised:                      0
% 11.97/2.00  sim_smt_subsumption:                    0
% 11.97/2.00  
%------------------------------------------------------------------------------
