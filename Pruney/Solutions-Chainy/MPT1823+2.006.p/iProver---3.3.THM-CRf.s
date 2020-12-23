%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:23 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  226 (4764 expanded)
%              Number of clauses        :  154 (1077 expanded)
%              Number of leaves         :   18 (1940 expanded)
%              Depth                    :   29
%              Number of atoms          : 1671 (59106 expanded)
%              Number of equality atoms :  656 (6217 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   30 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f35,f41,f40,f39,f38,f37])).

fof(f66,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f23])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f21])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f25])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f29])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f26])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_324,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_2,c_3])).

cnf(c_775,plain,
    ( v2_struct_0(X0_54)
    | ~ v1_xboole_0(u1_struct_0(X0_54))
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_324])).

cnf(c_11041,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_783,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1418,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_791,plain,
    ( m1_pre_topc(X0_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1411,plain,
    ( m1_pre_topc(X0_54,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_789,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1413,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f49])).

cnf(c_799,plain,
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
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1403,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_790,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X1_54,X2_54)
    | m1_pre_topc(X0_54,X2_54)
    | ~ v2_pre_topc(X2_54)
    | ~ l1_pre_topc(X2_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1412,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X1_54,X2_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) = iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_1617,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1403,c_1412])).

cnf(c_4859,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_54,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_1617])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_35,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_36,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5126,plain,
    ( v2_struct_0(X1_54) = iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
    | m1_pre_topc(X0_54,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4859,c_34,c_35,c_36,c_41,c_42])).

cnf(c_5127,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
    | m1_pre_topc(X0_54,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_5126])).

cnf(c_5138,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK0,X0_54,sK4)
    | m1_pre_topc(X0_54,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_5127])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_31,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_32,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_33,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5141,plain,
    ( m1_pre_topc(X0_54,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK0,X0_54,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5138,c_31,c_32,c_33])).

cnf(c_5142,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK0,X0_54,sK4)
    | m1_pre_topc(X0_54,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5141])).

cnf(c_5150,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    inference(superposition,[status(thm)],[c_1418,c_5142])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f48])).

cnf(c_800,plain,
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
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1402,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_2518,plain,
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
    inference(superposition,[status(thm)],[c_1413,c_1402])).

cnf(c_2963,plain,
    ( m1_pre_topc(X0_54,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2518,c_31,c_32,c_33,c_34,c_35,c_36,c_41,c_42])).

cnf(c_2964,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54)
    | m1_pre_topc(X0_54,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2963])).

cnf(c_2972,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_1418,c_2964])).

cnf(c_5158,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(light_normalisation,[status(thm)],[c_5150,c_2972])).

cnf(c_20,negated_conjecture,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_786,negated_conjecture,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f51])).

cnf(c_797,plain,
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
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1405,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_4733,plain,
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
    inference(superposition,[status(thm)],[c_786,c_1405])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_37,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_38,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_39,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_40,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4826,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_4733,c_31,c_32,c_33,c_37,c_38,c_39,c_40])).

cnf(c_4827,plain,
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
    inference(renaming,[status(thm)],[c_4826])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_792,plain,
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
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1410,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_3742,plain,
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
    inference(superposition,[status(thm)],[c_786,c_1410])).

cnf(c_3745,plain,
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
    inference(light_normalisation,[status(thm)],[c_3742,c_786])).

cnf(c_3750,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3745,c_31,c_32,c_33,c_37,c_38,c_39,c_40])).

cnf(c_3751,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3750])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_798,plain,
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
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1404,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_3249,plain,
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
    inference(superposition,[status(thm)],[c_786,c_1404])).

cnf(c_3842,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_3249,c_31,c_32,c_33,c_37,c_38,c_39,c_40])).

cnf(c_3843,plain,
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
    inference(renaming,[status(thm)],[c_3842])).

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

cnf(c_801,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
    | ~ v1_funct_2(X1_52,X0_53,X1_53)
    | ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | X0_52 = X1_52 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1401,plain,
    ( X0_52 = X1_52
    | r2_funct_2(X0_53,X1_53,X0_52,X1_52) != iProver_top
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | v1_funct_2(X1_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_2456,plain,
    ( sK4 = X0_52
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_1401])).

cnf(c_2918,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | sK4 = X0_52
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2456,c_41,c_42])).

cnf(c_2919,plain,
    ( sK4 = X0_52
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_2918])).

cnf(c_3863,plain,
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
    inference(superposition,[status(thm)],[c_3843,c_2919])).

cnf(c_4428,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_3863,c_34,c_35,c_36])).

cnf(c_4429,plain,
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
    inference(renaming,[status(thm)],[c_4428])).

cnf(c_4444,plain,
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
    inference(superposition,[status(thm)],[c_3751,c_4429])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5422,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4444,c_34,c_35,c_36,c_41,c_42,c_43])).

cnf(c_5423,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5422])).

cnf(c_5435,plain,
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
    inference(superposition,[status(thm)],[c_4827,c_5423])).

cnf(c_5529,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5435,c_34,c_35,c_36])).

cnf(c_5530,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5529])).

cnf(c_5683,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5158,c_5530])).

cnf(c_46,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_48,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_795,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1407,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_5720,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5158,c_1407])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_794,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_52),u1_struct_0(X3_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1408,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_52),u1_struct_0(X3_54),u1_struct_0(X1_54)) = iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_5721,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5158,c_1408])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_793,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
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
    | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1409,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_2535,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(sK0,X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1413,c_1409])).

cnf(c_1874,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(sK0,X1_54)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1875,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(sK0,X1_54) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1874])).

cnf(c_3110,plain,
    ( v1_funct_1(k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(sK0,X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2535,c_34,c_35,c_36,c_41,c_42,c_43,c_1875])).

cnf(c_3111,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(sK0,X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3110])).

cnf(c_5722,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5158,c_3111])).

cnf(c_6716,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5683,c_31,c_32,c_33,c_34,c_35,c_36,c_38,c_41,c_42,c_43,c_48,c_5720,c_5721,c_5722])).

cnf(c_6717,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6716])).

cnf(c_785,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1416,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_5149,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1416,c_5142])).

cnf(c_2971,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1416,c_2964])).

cnf(c_5161,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(light_normalisation,[status(thm)],[c_5149,c_2971])).

cnf(c_6720,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6717,c_5161])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f50])).

cnf(c_796,plain,
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
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2122,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK1))
    | ~ v1_funct_2(X1_52,u1_struct_0(X1_54),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_54,X2_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X2_54)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X2_54)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | v1_funct_1(k10_tmap_1(X2_54,sK1,X0_54,X1_54,X0_52,X1_52)) ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_2539,plain,
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
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_2540,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2539])).

cnf(c_6529,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5161,c_1407])).

cnf(c_6530,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5161,c_1408])).

cnf(c_6531,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5161,c_3111])).

cnf(c_6727,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6720,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_48,c_2540,c_5720,c_5721,c_5722,c_6529,c_6530,c_6531])).

cnf(c_4,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_342,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) != X4
    | u1_struct_0(sK1) != X5
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_343,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | sK4 != k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_774,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | sK4 != k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_804,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | sP0_iProver_split
    | sK4 != k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_774])).

cnf(c_1427,plain,
    ( sK4 != k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_803,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_774])).

cnf(c_1428,plain,
    ( v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_1485,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1428,c_786])).

cnf(c_1636,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1427,c_1485])).

cnf(c_818,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(X1_52)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_1848,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0_52 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_1849,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0_52
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1848])).

cnf(c_1851,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1849])).

cnf(c_2289,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1636,c_41,c_1851])).

cnf(c_2290,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2289])).

cnf(c_6730,plain,
    ( sK4 != sK4
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6727,c_2290])).

cnf(c_6731,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6730])).

cnf(c_6738,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6731])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11041,c_6738,c_17,c_18,c_25,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.01/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/0.98  
% 4.01/0.98  ------  iProver source info
% 4.01/0.98  
% 4.01/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.01/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/0.98  git: non_committed_changes: false
% 4.01/0.98  git: last_make_outside_of_git: false
% 4.01/0.98  
% 4.01/0.98  ------ 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options
% 4.01/0.98  
% 4.01/0.98  --out_options                           all
% 4.01/0.98  --tptp_safe_out                         true
% 4.01/0.98  --problem_path                          ""
% 4.01/0.98  --include_path                          ""
% 4.01/0.98  --clausifier                            res/vclausify_rel
% 4.01/0.98  --clausifier_options                    --mode clausify
% 4.01/0.98  --stdin                                 false
% 4.01/0.98  --stats_out                             all
% 4.01/0.98  
% 4.01/0.98  ------ General Options
% 4.01/0.98  
% 4.01/0.98  --fof                                   false
% 4.01/0.98  --time_out_real                         305.
% 4.01/0.98  --time_out_virtual                      -1.
% 4.01/0.98  --symbol_type_check                     false
% 4.01/0.98  --clausify_out                          false
% 4.01/0.98  --sig_cnt_out                           false
% 4.01/0.98  --trig_cnt_out                          false
% 4.01/0.98  --trig_cnt_out_tolerance                1.
% 4.01/0.98  --trig_cnt_out_sk_spl                   false
% 4.01/0.98  --abstr_cl_out                          false
% 4.01/0.98  
% 4.01/0.98  ------ Global Options
% 4.01/0.98  
% 4.01/0.98  --schedule                              default
% 4.01/0.98  --add_important_lit                     false
% 4.01/0.98  --prop_solver_per_cl                    1000
% 4.01/0.98  --min_unsat_core                        false
% 4.01/0.98  --soft_assumptions                      false
% 4.01/0.98  --soft_lemma_size                       3
% 4.01/0.98  --prop_impl_unit_size                   0
% 4.01/0.98  --prop_impl_unit                        []
% 4.01/0.98  --share_sel_clauses                     true
% 4.01/0.98  --reset_solvers                         false
% 4.01/0.98  --bc_imp_inh                            [conj_cone]
% 4.01/0.98  --conj_cone_tolerance                   3.
% 4.01/0.98  --extra_neg_conj                        none
% 4.01/0.98  --large_theory_mode                     true
% 4.01/0.98  --prolific_symb_bound                   200
% 4.01/0.98  --lt_threshold                          2000
% 4.01/0.98  --clause_weak_htbl                      true
% 4.01/0.98  --gc_record_bc_elim                     false
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing Options
% 4.01/0.98  
% 4.01/0.98  --preprocessing_flag                    true
% 4.01/0.98  --time_out_prep_mult                    0.1
% 4.01/0.98  --splitting_mode                        input
% 4.01/0.98  --splitting_grd                         true
% 4.01/0.98  --splitting_cvd                         false
% 4.01/0.98  --splitting_cvd_svl                     false
% 4.01/0.98  --splitting_nvd                         32
% 4.01/0.98  --sub_typing                            true
% 4.01/0.98  --prep_gs_sim                           true
% 4.01/0.98  --prep_unflatten                        true
% 4.01/0.98  --prep_res_sim                          true
% 4.01/0.98  --prep_upred                            true
% 4.01/0.98  --prep_sem_filter                       exhaustive
% 4.01/0.98  --prep_sem_filter_out                   false
% 4.01/0.98  --pred_elim                             true
% 4.01/0.98  --res_sim_input                         true
% 4.01/0.98  --eq_ax_congr_red                       true
% 4.01/0.98  --pure_diseq_elim                       true
% 4.01/0.98  --brand_transform                       false
% 4.01/0.98  --non_eq_to_eq                          false
% 4.01/0.98  --prep_def_merge                        true
% 4.01/0.98  --prep_def_merge_prop_impl              false
% 4.01/0.98  --prep_def_merge_mbd                    true
% 4.01/0.98  --prep_def_merge_tr_red                 false
% 4.01/0.98  --prep_def_merge_tr_cl                  false
% 4.01/0.98  --smt_preprocessing                     true
% 4.01/0.98  --smt_ac_axioms                         fast
% 4.01/0.98  --preprocessed_out                      false
% 4.01/0.98  --preprocessed_stats                    false
% 4.01/0.98  
% 4.01/0.98  ------ Abstraction refinement Options
% 4.01/0.98  
% 4.01/0.98  --abstr_ref                             []
% 4.01/0.98  --abstr_ref_prep                        false
% 4.01/0.98  --abstr_ref_until_sat                   false
% 4.01/0.98  --abstr_ref_sig_restrict                funpre
% 4.01/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/0.98  --abstr_ref_under                       []
% 4.01/0.98  
% 4.01/0.98  ------ SAT Options
% 4.01/0.98  
% 4.01/0.98  --sat_mode                              false
% 4.01/0.98  --sat_fm_restart_options                ""
% 4.01/0.98  --sat_gr_def                            false
% 4.01/0.98  --sat_epr_types                         true
% 4.01/0.98  --sat_non_cyclic_types                  false
% 4.01/0.98  --sat_finite_models                     false
% 4.01/0.98  --sat_fm_lemmas                         false
% 4.01/0.98  --sat_fm_prep                           false
% 4.01/0.98  --sat_fm_uc_incr                        true
% 4.01/0.98  --sat_out_model                         small
% 4.01/0.98  --sat_out_clauses                       false
% 4.01/0.98  
% 4.01/0.98  ------ QBF Options
% 4.01/0.98  
% 4.01/0.98  --qbf_mode                              false
% 4.01/0.98  --qbf_elim_univ                         false
% 4.01/0.98  --qbf_dom_inst                          none
% 4.01/0.98  --qbf_dom_pre_inst                      false
% 4.01/0.98  --qbf_sk_in                             false
% 4.01/0.98  --qbf_pred_elim                         true
% 4.01/0.98  --qbf_split                             512
% 4.01/0.98  
% 4.01/0.98  ------ BMC1 Options
% 4.01/0.98  
% 4.01/0.98  --bmc1_incremental                      false
% 4.01/0.98  --bmc1_axioms                           reachable_all
% 4.01/0.98  --bmc1_min_bound                        0
% 4.01/0.98  --bmc1_max_bound                        -1
% 4.01/0.98  --bmc1_max_bound_default                -1
% 4.01/0.98  --bmc1_symbol_reachability              true
% 4.01/0.98  --bmc1_property_lemmas                  false
% 4.01/0.98  --bmc1_k_induction                      false
% 4.01/0.98  --bmc1_non_equiv_states                 false
% 4.01/0.98  --bmc1_deadlock                         false
% 4.01/0.98  --bmc1_ucm                              false
% 4.01/0.98  --bmc1_add_unsat_core                   none
% 4.01/0.98  --bmc1_unsat_core_children              false
% 4.01/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/0.98  --bmc1_out_stat                         full
% 4.01/0.98  --bmc1_ground_init                      false
% 4.01/0.98  --bmc1_pre_inst_next_state              false
% 4.01/0.98  --bmc1_pre_inst_state                   false
% 4.01/0.98  --bmc1_pre_inst_reach_state             false
% 4.01/0.98  --bmc1_out_unsat_core                   false
% 4.01/0.98  --bmc1_aig_witness_out                  false
% 4.01/0.98  --bmc1_verbose                          false
% 4.01/0.98  --bmc1_dump_clauses_tptp                false
% 4.01/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.01/0.98  --bmc1_dump_file                        -
% 4.01/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.01/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.01/0.98  --bmc1_ucm_extend_mode                  1
% 4.01/0.98  --bmc1_ucm_init_mode                    2
% 4.01/0.98  --bmc1_ucm_cone_mode                    none
% 4.01/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.01/0.98  --bmc1_ucm_relax_model                  4
% 4.01/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.01/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/0.98  --bmc1_ucm_layered_model                none
% 4.01/0.98  --bmc1_ucm_max_lemma_size               10
% 4.01/0.98  
% 4.01/0.98  ------ AIG Options
% 4.01/0.98  
% 4.01/0.98  --aig_mode                              false
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation Options
% 4.01/0.98  
% 4.01/0.98  --instantiation_flag                    true
% 4.01/0.98  --inst_sos_flag                         false
% 4.01/0.98  --inst_sos_phase                        true
% 4.01/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel_side                     num_symb
% 4.01/0.98  --inst_solver_per_active                1400
% 4.01/0.98  --inst_solver_calls_frac                1.
% 4.01/0.98  --inst_passive_queue_type               priority_queues
% 4.01/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/0.98  --inst_passive_queues_freq              [25;2]
% 4.01/0.98  --inst_dismatching                      true
% 4.01/0.98  --inst_eager_unprocessed_to_passive     true
% 4.01/0.98  --inst_prop_sim_given                   true
% 4.01/0.98  --inst_prop_sim_new                     false
% 4.01/0.98  --inst_subs_new                         false
% 4.01/0.98  --inst_eq_res_simp                      false
% 4.01/0.98  --inst_subs_given                       false
% 4.01/0.98  --inst_orphan_elimination               true
% 4.01/0.98  --inst_learning_loop_flag               true
% 4.01/0.98  --inst_learning_start                   3000
% 4.01/0.98  --inst_learning_factor                  2
% 4.01/0.98  --inst_start_prop_sim_after_learn       3
% 4.01/0.98  --inst_sel_renew                        solver
% 4.01/0.98  --inst_lit_activity_flag                true
% 4.01/0.98  --inst_restr_to_given                   false
% 4.01/0.98  --inst_activity_threshold               500
% 4.01/0.98  --inst_out_proof                        true
% 4.01/0.98  
% 4.01/0.98  ------ Resolution Options
% 4.01/0.98  
% 4.01/0.98  --resolution_flag                       true
% 4.01/0.98  --res_lit_sel                           adaptive
% 4.01/0.98  --res_lit_sel_side                      none
% 4.01/0.98  --res_ordering                          kbo
% 4.01/0.98  --res_to_prop_solver                    active
% 4.01/0.98  --res_prop_simpl_new                    false
% 4.01/0.98  --res_prop_simpl_given                  true
% 4.01/0.98  --res_passive_queue_type                priority_queues
% 4.01/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/0.98  --res_passive_queues_freq               [15;5]
% 4.01/0.98  --res_forward_subs                      full
% 4.01/0.98  --res_backward_subs                     full
% 4.01/0.98  --res_forward_subs_resolution           true
% 4.01/0.98  --res_backward_subs_resolution          true
% 4.01/0.98  --res_orphan_elimination                true
% 4.01/0.98  --res_time_limit                        2.
% 4.01/0.98  --res_out_proof                         true
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Options
% 4.01/0.98  
% 4.01/0.98  --superposition_flag                    true
% 4.01/0.98  --sup_passive_queue_type                priority_queues
% 4.01/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.01/0.98  --demod_completeness_check              fast
% 4.01/0.98  --demod_use_ground                      true
% 4.01/0.98  --sup_to_prop_solver                    passive
% 4.01/0.98  --sup_prop_simpl_new                    true
% 4.01/0.98  --sup_prop_simpl_given                  true
% 4.01/0.98  --sup_fun_splitting                     false
% 4.01/0.98  --sup_smt_interval                      50000
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Simplification Setup
% 4.01/0.98  
% 4.01/0.98  --sup_indices_passive                   []
% 4.01/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_full_bw                           [BwDemod]
% 4.01/0.98  --sup_immed_triv                        [TrivRules]
% 4.01/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_immed_bw_main                     []
% 4.01/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  
% 4.01/0.98  ------ Combination Options
% 4.01/0.98  
% 4.01/0.98  --comb_res_mult                         3
% 4.01/0.98  --comb_sup_mult                         2
% 4.01/0.98  --comb_inst_mult                        10
% 4.01/0.98  
% 4.01/0.98  ------ Debug Options
% 4.01/0.98  
% 4.01/0.98  --dbg_backtrace                         false
% 4.01/0.98  --dbg_dump_prop_clauses                 false
% 4.01/0.98  --dbg_dump_prop_clauses_file            -
% 4.01/0.98  --dbg_out_stat                          false
% 4.01/0.98  ------ Parsing...
% 4.01/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.01/0.98  ------ Proving...
% 4.01/0.98  ------ Problem Properties 
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  clauses                                 30
% 4.01/0.98  conjectures                             14
% 4.01/0.98  EPR                                     13
% 4.01/0.98  Horn                                    20
% 4.01/0.98  unary                                   14
% 4.01/0.98  binary                                  1
% 4.01/0.98  lits                                    171
% 4.01/0.98  lits eq                                 5
% 4.01/0.98  fd_pure                                 0
% 4.01/0.98  fd_pseudo                               0
% 4.01/0.98  fd_cond                                 0
% 4.01/0.98  fd_pseudo_cond                          1
% 4.01/0.98  AC symbols                              0
% 4.01/0.98  
% 4.01/0.98  ------ Schedule dynamic 5 is on 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  ------ 
% 4.01/0.98  Current options:
% 4.01/0.98  ------ 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options
% 4.01/0.98  
% 4.01/0.98  --out_options                           all
% 4.01/0.98  --tptp_safe_out                         true
% 4.01/0.98  --problem_path                          ""
% 4.01/0.98  --include_path                          ""
% 4.01/0.98  --clausifier                            res/vclausify_rel
% 4.01/0.98  --clausifier_options                    --mode clausify
% 4.01/0.98  --stdin                                 false
% 4.01/0.98  --stats_out                             all
% 4.01/0.98  
% 4.01/0.98  ------ General Options
% 4.01/0.98  
% 4.01/0.98  --fof                                   false
% 4.01/0.98  --time_out_real                         305.
% 4.01/0.98  --time_out_virtual                      -1.
% 4.01/0.98  --symbol_type_check                     false
% 4.01/0.98  --clausify_out                          false
% 4.01/0.98  --sig_cnt_out                           false
% 4.01/0.98  --trig_cnt_out                          false
% 4.01/0.98  --trig_cnt_out_tolerance                1.
% 4.01/0.98  --trig_cnt_out_sk_spl                   false
% 4.01/0.98  --abstr_cl_out                          false
% 4.01/0.98  
% 4.01/0.98  ------ Global Options
% 4.01/0.98  
% 4.01/0.98  --schedule                              default
% 4.01/0.98  --add_important_lit                     false
% 4.01/0.98  --prop_solver_per_cl                    1000
% 4.01/0.98  --min_unsat_core                        false
% 4.01/0.98  --soft_assumptions                      false
% 4.01/0.98  --soft_lemma_size                       3
% 4.01/0.98  --prop_impl_unit_size                   0
% 4.01/0.98  --prop_impl_unit                        []
% 4.01/0.98  --share_sel_clauses                     true
% 4.01/0.98  --reset_solvers                         false
% 4.01/0.98  --bc_imp_inh                            [conj_cone]
% 4.01/0.98  --conj_cone_tolerance                   3.
% 4.01/0.98  --extra_neg_conj                        none
% 4.01/0.98  --large_theory_mode                     true
% 4.01/0.98  --prolific_symb_bound                   200
% 4.01/0.98  --lt_threshold                          2000
% 4.01/0.98  --clause_weak_htbl                      true
% 4.01/0.98  --gc_record_bc_elim                     false
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing Options
% 4.01/0.98  
% 4.01/0.98  --preprocessing_flag                    true
% 4.01/0.98  --time_out_prep_mult                    0.1
% 4.01/0.98  --splitting_mode                        input
% 4.01/0.98  --splitting_grd                         true
% 4.01/0.98  --splitting_cvd                         false
% 4.01/0.98  --splitting_cvd_svl                     false
% 4.01/0.98  --splitting_nvd                         32
% 4.01/0.98  --sub_typing                            true
% 4.01/0.98  --prep_gs_sim                           true
% 4.01/0.98  --prep_unflatten                        true
% 4.01/0.98  --prep_res_sim                          true
% 4.01/0.98  --prep_upred                            true
% 4.01/0.98  --prep_sem_filter                       exhaustive
% 4.01/0.98  --prep_sem_filter_out                   false
% 4.01/0.98  --pred_elim                             true
% 4.01/0.98  --res_sim_input                         true
% 4.01/0.98  --eq_ax_congr_red                       true
% 4.01/0.98  --pure_diseq_elim                       true
% 4.01/0.98  --brand_transform                       false
% 4.01/0.98  --non_eq_to_eq                          false
% 4.01/0.98  --prep_def_merge                        true
% 4.01/0.98  --prep_def_merge_prop_impl              false
% 4.01/0.98  --prep_def_merge_mbd                    true
% 4.01/0.98  --prep_def_merge_tr_red                 false
% 4.01/0.98  --prep_def_merge_tr_cl                  false
% 4.01/0.98  --smt_preprocessing                     true
% 4.01/0.98  --smt_ac_axioms                         fast
% 4.01/0.98  --preprocessed_out                      false
% 4.01/0.98  --preprocessed_stats                    false
% 4.01/0.98  
% 4.01/0.98  ------ Abstraction refinement Options
% 4.01/0.98  
% 4.01/0.98  --abstr_ref                             []
% 4.01/0.98  --abstr_ref_prep                        false
% 4.01/0.98  --abstr_ref_until_sat                   false
% 4.01/0.98  --abstr_ref_sig_restrict                funpre
% 4.01/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/0.98  --abstr_ref_under                       []
% 4.01/0.98  
% 4.01/0.98  ------ SAT Options
% 4.01/0.98  
% 4.01/0.98  --sat_mode                              false
% 4.01/0.98  --sat_fm_restart_options                ""
% 4.01/0.98  --sat_gr_def                            false
% 4.01/0.98  --sat_epr_types                         true
% 4.01/0.98  --sat_non_cyclic_types                  false
% 4.01/0.98  --sat_finite_models                     false
% 4.01/0.98  --sat_fm_lemmas                         false
% 4.01/0.98  --sat_fm_prep                           false
% 4.01/0.98  --sat_fm_uc_incr                        true
% 4.01/0.98  --sat_out_model                         small
% 4.01/0.98  --sat_out_clauses                       false
% 4.01/0.98  
% 4.01/0.98  ------ QBF Options
% 4.01/0.98  
% 4.01/0.98  --qbf_mode                              false
% 4.01/0.98  --qbf_elim_univ                         false
% 4.01/0.98  --qbf_dom_inst                          none
% 4.01/0.98  --qbf_dom_pre_inst                      false
% 4.01/0.98  --qbf_sk_in                             false
% 4.01/0.98  --qbf_pred_elim                         true
% 4.01/0.98  --qbf_split                             512
% 4.01/0.98  
% 4.01/0.98  ------ BMC1 Options
% 4.01/0.98  
% 4.01/0.98  --bmc1_incremental                      false
% 4.01/0.98  --bmc1_axioms                           reachable_all
% 4.01/0.98  --bmc1_min_bound                        0
% 4.01/0.98  --bmc1_max_bound                        -1
% 4.01/0.98  --bmc1_max_bound_default                -1
% 4.01/0.98  --bmc1_symbol_reachability              true
% 4.01/0.98  --bmc1_property_lemmas                  false
% 4.01/0.98  --bmc1_k_induction                      false
% 4.01/0.98  --bmc1_non_equiv_states                 false
% 4.01/0.98  --bmc1_deadlock                         false
% 4.01/0.98  --bmc1_ucm                              false
% 4.01/0.98  --bmc1_add_unsat_core                   none
% 4.01/0.98  --bmc1_unsat_core_children              false
% 4.01/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/0.98  --bmc1_out_stat                         full
% 4.01/0.98  --bmc1_ground_init                      false
% 4.01/0.98  --bmc1_pre_inst_next_state              false
% 4.01/0.98  --bmc1_pre_inst_state                   false
% 4.01/0.98  --bmc1_pre_inst_reach_state             false
% 4.01/0.98  --bmc1_out_unsat_core                   false
% 4.01/0.98  --bmc1_aig_witness_out                  false
% 4.01/0.98  --bmc1_verbose                          false
% 4.01/0.98  --bmc1_dump_clauses_tptp                false
% 4.01/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.01/0.98  --bmc1_dump_file                        -
% 4.01/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.01/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.01/0.98  --bmc1_ucm_extend_mode                  1
% 4.01/0.98  --bmc1_ucm_init_mode                    2
% 4.01/0.98  --bmc1_ucm_cone_mode                    none
% 4.01/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.01/0.98  --bmc1_ucm_relax_model                  4
% 4.01/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.01/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/0.98  --bmc1_ucm_layered_model                none
% 4.01/0.98  --bmc1_ucm_max_lemma_size               10
% 4.01/0.98  
% 4.01/0.98  ------ AIG Options
% 4.01/0.98  
% 4.01/0.98  --aig_mode                              false
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation Options
% 4.01/0.98  
% 4.01/0.98  --instantiation_flag                    true
% 4.01/0.98  --inst_sos_flag                         false
% 4.01/0.98  --inst_sos_phase                        true
% 4.01/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel_side                     none
% 4.01/0.98  --inst_solver_per_active                1400
% 4.01/0.98  --inst_solver_calls_frac                1.
% 4.01/0.98  --inst_passive_queue_type               priority_queues
% 4.01/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/0.98  --inst_passive_queues_freq              [25;2]
% 4.01/0.98  --inst_dismatching                      true
% 4.01/0.98  --inst_eager_unprocessed_to_passive     true
% 4.01/0.98  --inst_prop_sim_given                   true
% 4.01/0.98  --inst_prop_sim_new                     false
% 4.01/0.98  --inst_subs_new                         false
% 4.01/0.98  --inst_eq_res_simp                      false
% 4.01/0.98  --inst_subs_given                       false
% 4.01/0.98  --inst_orphan_elimination               true
% 4.01/0.98  --inst_learning_loop_flag               true
% 4.01/0.98  --inst_learning_start                   3000
% 4.01/0.98  --inst_learning_factor                  2
% 4.01/0.98  --inst_start_prop_sim_after_learn       3
% 4.01/0.98  --inst_sel_renew                        solver
% 4.01/0.98  --inst_lit_activity_flag                true
% 4.01/0.98  --inst_restr_to_given                   false
% 4.01/0.98  --inst_activity_threshold               500
% 4.01/0.98  --inst_out_proof                        true
% 4.01/0.98  
% 4.01/0.98  ------ Resolution Options
% 4.01/0.98  
% 4.01/0.98  --resolution_flag                       false
% 4.01/0.98  --res_lit_sel                           adaptive
% 4.01/0.98  --res_lit_sel_side                      none
% 4.01/0.98  --res_ordering                          kbo
% 4.01/0.98  --res_to_prop_solver                    active
% 4.01/0.98  --res_prop_simpl_new                    false
% 4.01/0.98  --res_prop_simpl_given                  true
% 4.01/0.98  --res_passive_queue_type                priority_queues
% 4.01/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/0.98  --res_passive_queues_freq               [15;5]
% 4.01/0.98  --res_forward_subs                      full
% 4.01/0.98  --res_backward_subs                     full
% 4.01/0.98  --res_forward_subs_resolution           true
% 4.01/0.98  --res_backward_subs_resolution          true
% 4.01/0.98  --res_orphan_elimination                true
% 4.01/0.98  --res_time_limit                        2.
% 4.01/0.98  --res_out_proof                         true
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Options
% 4.01/0.98  
% 4.01/0.98  --superposition_flag                    true
% 4.01/0.98  --sup_passive_queue_type                priority_queues
% 4.01/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.01/0.98  --demod_completeness_check              fast
% 4.01/0.98  --demod_use_ground                      true
% 4.01/0.98  --sup_to_prop_solver                    passive
% 4.01/0.98  --sup_prop_simpl_new                    true
% 4.01/0.98  --sup_prop_simpl_given                  true
% 4.01/0.98  --sup_fun_splitting                     false
% 4.01/0.98  --sup_smt_interval                      50000
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Simplification Setup
% 4.01/0.98  
% 4.01/0.98  --sup_indices_passive                   []
% 4.01/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_full_bw                           [BwDemod]
% 4.01/0.98  --sup_immed_triv                        [TrivRules]
% 4.01/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_immed_bw_main                     []
% 4.01/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  
% 4.01/0.98  ------ Combination Options
% 4.01/0.98  
% 4.01/0.98  --comb_res_mult                         3
% 4.01/0.98  --comb_sup_mult                         2
% 4.01/0.98  --comb_inst_mult                        10
% 4.01/0.98  
% 4.01/0.98  ------ Debug Options
% 4.01/0.98  
% 4.01/0.98  --dbg_backtrace                         false
% 4.01/0.98  --dbg_dump_prop_clauses                 false
% 4.01/0.98  --dbg_dump_prop_clauses_file            -
% 4.01/0.98  --dbg_out_stat                          false
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  ------ Proving...
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS status Theorem for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  fof(f2,axiom,(
% 4.01/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f16,plain,(
% 4.01/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f2])).
% 4.01/0.98  
% 4.01/0.98  fof(f45,plain,(
% 4.01/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f16])).
% 4.01/0.98  
% 4.01/0.98  fof(f3,axiom,(
% 4.01/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f17,plain,(
% 4.01/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f3])).
% 4.01/0.98  
% 4.01/0.98  fof(f18,plain,(
% 4.01/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f17])).
% 4.01/0.98  
% 4.01/0.98  fof(f46,plain,(
% 4.01/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f18])).
% 4.01/0.98  
% 4.01/0.98  fof(f12,conjecture,(
% 4.01/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f13,negated_conjecture,(
% 4.01/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 4.01/0.98    inference(negated_conjecture,[],[f12])).
% 4.01/0.98  
% 4.01/0.98  fof(f34,plain,(
% 4.01/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f13])).
% 4.01/0.98  
% 4.01/0.98  fof(f35,plain,(
% 4.01/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f34])).
% 4.01/0.98  
% 4.01/0.98  fof(f41,plain,(
% 4.01/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),sK4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,sK4,X2),k2_tmap_1(X0,X1,sK4,X3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f40,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,sK3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,sK3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,sK3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,sK3) = X0 & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f39,plain,(
% 4.01/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,sK2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,sK2,X3,k2_tmap_1(X0,X1,X4,sK2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,sK2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f38,plain,(
% 4.01/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(X0,sK1,X2,X3,k2_tmap_1(X0,sK1,X4,X2),k2_tmap_1(X0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f37,plain,(
% 4.01/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(sK0,X2,X3) = sK0 & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f42,plain,(
% 4.01/0.98    ((((~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & k1_tsep_1(sK0,sK2,sK3) = sK0 & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 4.01/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f35,f41,f40,f39,f38,f37])).
% 4.01/0.98  
% 4.01/0.98  fof(f66,plain,(
% 4.01/0.98    m1_pre_topc(sK2,sK0)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f10,axiom,(
% 4.01/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f31,plain,(
% 4.01/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f10])).
% 4.01/0.98  
% 4.01/0.98  fof(f57,plain,(
% 4.01/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f31])).
% 4.01/0.98  
% 4.01/0.98  fof(f72,plain,(
% 4.01/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f6,axiom,(
% 4.01/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f23,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f6])).
% 4.01/0.98  
% 4.01/0.98  fof(f24,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f23])).
% 4.01/0.98  
% 4.01/0.98  fof(f49,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f24])).
% 4.01/0.98  
% 4.01/0.98  fof(f11,axiom,(
% 4.01/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f32,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f11])).
% 4.01/0.98  
% 4.01/0.98  fof(f33,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.01/0.98    inference(flattening,[],[f32])).
% 4.01/0.98  
% 4.01/0.98  fof(f58,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f33])).
% 4.01/0.98  
% 4.01/0.98  fof(f62,plain,(
% 4.01/0.98    ~v2_struct_0(sK1)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f63,plain,(
% 4.01/0.98    v2_pre_topc(sK1)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f64,plain,(
% 4.01/0.98    l1_pre_topc(sK1)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f70,plain,(
% 4.01/0.98    v1_funct_1(sK4)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f71,plain,(
% 4.01/0.98    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f59,plain,(
% 4.01/0.98    ~v2_struct_0(sK0)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f60,plain,(
% 4.01/0.98    v2_pre_topc(sK0)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f61,plain,(
% 4.01/0.98    l1_pre_topc(sK0)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f5,axiom,(
% 4.01/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f21,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f5])).
% 4.01/0.98  
% 4.01/0.98  fof(f22,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f21])).
% 4.01/0.98  
% 4.01/0.98  fof(f48,plain,(
% 4.01/0.98    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f22])).
% 4.01/0.98  
% 4.01/0.98  fof(f69,plain,(
% 4.01/0.98    k1_tsep_1(sK0,sK2,sK3) = sK0),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f7,axiom,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f25,plain,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f7])).
% 4.01/0.98  
% 4.01/0.98  fof(f26,plain,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f25])).
% 4.01/0.98  
% 4.01/0.98  fof(f51,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f26])).
% 4.01/0.98  
% 4.01/0.98  fof(f65,plain,(
% 4.01/0.98    ~v2_struct_0(sK2)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f67,plain,(
% 4.01/0.98    ~v2_struct_0(sK3)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f68,plain,(
% 4.01/0.98    m1_pre_topc(sK3,sK0)),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  fof(f9,axiom,(
% 4.01/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f29,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f9])).
% 4.01/0.98  
% 4.01/0.98  fof(f30,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f29])).
% 4.01/0.98  
% 4.01/0.98  fof(f56,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f30])).
% 4.01/0.98  
% 4.01/0.98  fof(f52,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f26])).
% 4.01/0.98  
% 4.01/0.98  fof(f1,axiom,(
% 4.01/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f14,plain,(
% 4.01/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.01/0.98    inference(ennf_transformation,[],[f1])).
% 4.01/0.98  
% 4.01/0.98  fof(f15,plain,(
% 4.01/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.01/0.98    inference(flattening,[],[f14])).
% 4.01/0.98  
% 4.01/0.98  fof(f36,plain,(
% 4.01/0.98    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.01/0.98    inference(nnf_transformation,[],[f15])).
% 4.01/0.98  
% 4.01/0.98  fof(f43,plain,(
% 4.01/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f36])).
% 4.01/0.98  
% 4.01/0.98  fof(f8,axiom,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f27,plain,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f8])).
% 4.01/0.98  
% 4.01/0.98  fof(f28,plain,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.01/0.98    inference(flattening,[],[f27])).
% 4.01/0.98  
% 4.01/0.98  fof(f55,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f28])).
% 4.01/0.98  
% 4.01/0.98  fof(f54,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f28])).
% 4.01/0.98  
% 4.01/0.98  fof(f53,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f28])).
% 4.01/0.98  
% 4.01/0.98  fof(f50,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f26])).
% 4.01/0.98  
% 4.01/0.98  fof(f4,axiom,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f19,plain,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 4.01/0.98    inference(ennf_transformation,[],[f4])).
% 4.01/0.98  
% 4.01/0.98  fof(f20,plain,(
% 4.01/0.98    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 4.01/0.98    inference(flattening,[],[f19])).
% 4.01/0.98  
% 4.01/0.98  fof(f47,plain,(
% 4.01/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f20])).
% 4.01/0.98  
% 4.01/0.98  fof(f73,plain,(
% 4.01/0.98    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 4.01/0.98    inference(cnf_transformation,[],[f42])).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2,plain,
% 4.01/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f45]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3,plain,
% 4.01/0.98      ( v2_struct_0(X0)
% 4.01/0.98      | ~ v1_xboole_0(u1_struct_0(X0))
% 4.01/0.98      | ~ l1_struct_0(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f46]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_324,plain,
% 4.01/0.98      ( v2_struct_0(X0)
% 4.01/0.98      | ~ v1_xboole_0(u1_struct_0(X0))
% 4.01/0.98      | ~ l1_pre_topc(X0) ),
% 4.01/0.98      inference(resolution,[status(thm)],[c_2,c_3]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_775,plain,
% 4.01/0.98      ( v2_struct_0(X0_54)
% 4.01/0.98      | ~ v1_xboole_0(u1_struct_0(X0_54))
% 4.01/0.98      | ~ l1_pre_topc(X0_54) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_324]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_11041,plain,
% 4.01/0.98      ( v2_struct_0(sK1)
% 4.01/0.98      | ~ v1_xboole_0(u1_struct_0(sK1))
% 4.01/0.98      | ~ l1_pre_topc(sK1) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_775]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_23,negated_conjecture,
% 4.01/0.98      ( m1_pre_topc(sK2,sK0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f66]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_783,negated_conjecture,
% 4.01/0.98      ( m1_pre_topc(sK2,sK0) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1418,plain,
% 4.01/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_14,plain,
% 4.01/0.98      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f57]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_791,plain,
% 4.01/0.98      ( m1_pre_topc(X0_54,X0_54) | ~ l1_pre_topc(X0_54) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1411,plain,
% 4.01/0.98      ( m1_pre_topc(X0_54,X0_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0_54) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_17,negated_conjecture,
% 4.01/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 4.01/0.98      inference(cnf_transformation,[],[f72]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_789,negated_conjecture,
% 4.01/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1413,plain,
% 4.01/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.01/0.98      | ~ m1_pre_topc(X3,X4)
% 4.01/0.98      | ~ m1_pre_topc(X3,X1)
% 4.01/0.98      | ~ m1_pre_topc(X1,X4)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.01/0.98      | ~ v2_pre_topc(X2)
% 4.01/0.98      | ~ v2_pre_topc(X4)
% 4.01/0.98      | v2_struct_0(X4)
% 4.01/0.98      | v2_struct_0(X2)
% 4.01/0.98      | ~ l1_pre_topc(X4)
% 4.01/0.98      | ~ l1_pre_topc(X2)
% 4.01/0.98      | ~ v1_funct_1(X0)
% 4.01/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f49]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_799,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.01/0.98      | ~ m1_pre_topc(X2_54,X0_54)
% 4.01/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 4.01/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ v2_pre_topc(X3_54)
% 4.01/0.98      | ~ v2_pre_topc(X1_54)
% 4.01/0.98      | v2_struct_0(X3_54)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | ~ l1_pre_topc(X3_54)
% 4.01/0.98      | ~ l1_pre_topc(X1_54)
% 4.01/0.98      | ~ v1_funct_1(X0_52)
% 4.01/0.98      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1403,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X3_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_15,plain,
% 4.01/0.98      ( ~ m1_pre_topc(X0,X1)
% 4.01/0.98      | ~ m1_pre_topc(X1,X2)
% 4.01/0.98      | m1_pre_topc(X0,X2)
% 4.01/0.98      | ~ v2_pre_topc(X2)
% 4.01/0.98      | ~ l1_pre_topc(X2) ),
% 4.01/0.98      inference(cnf_transformation,[],[f58]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_790,plain,
% 4.01/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 4.01/0.98      | ~ m1_pre_topc(X1_54,X2_54)
% 4.01/0.98      | m1_pre_topc(X0_54,X2_54)
% 4.01/0.98      | ~ v2_pre_topc(X2_54)
% 4.01/0.98      | ~ l1_pre_topc(X2_54) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1412,plain,
% 4.01/0.98      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X2_54) = iProver_top
% 4.01/0.98      | v2_pre_topc(X2_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X2_54) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1617,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X3_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(forward_subsumption_resolution,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_1403,c_1412]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4859,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
% 4.01/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,X1_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1413,c_1617]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_27,negated_conjecture,
% 4.01/0.98      ( ~ v2_struct_0(sK1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f62]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_34,plain,
% 4.01/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_26,negated_conjecture,
% 4.01/0.98      ( v2_pre_topc(sK1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f63]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_35,plain,
% 4.01/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_25,negated_conjecture,
% 4.01/0.98      ( l1_pre_topc(sK1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f64]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_36,plain,
% 4.01/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_19,negated_conjecture,
% 4.01/0.98      ( v1_funct_1(sK4) ),
% 4.01/0.98      inference(cnf_transformation,[],[f70]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_41,plain,
% 4.01/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_18,negated_conjecture,
% 4.01/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 4.01/0.98      inference(cnf_transformation,[],[f71]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_42,plain,
% 4.01/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5126,plain,
% 4.01/0.98      ( v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
% 4.01/0.98      | m1_pre_topc(X0_54,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,X1_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_4859,c_34,c_35,c_36,c_41,c_42]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5127,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
% 4.01/0.98      | m1_pre_topc(X0_54,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,X1_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_5126]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5138,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK0,X0_54,sK4)
% 4.01/0.98      | m1_pre_topc(X0_54,sK0) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1411,c_5127]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_30,negated_conjecture,
% 4.01/0.98      ( ~ v2_struct_0(sK0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f59]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_31,plain,
% 4.01/0.98      ( v2_struct_0(sK0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_29,negated_conjecture,
% 4.01/0.98      ( v2_pre_topc(sK0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f60]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_32,plain,
% 4.01/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_28,negated_conjecture,
% 4.01/0.98      ( l1_pre_topc(sK0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f61]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_33,plain,
% 4.01/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5141,plain,
% 4.01/0.98      ( m1_pre_topc(X0_54,sK0) != iProver_top
% 4.01/0.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK0,X0_54,sK4) ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_5138,c_31,c_32,c_33]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5142,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK0,X0_54,sK4)
% 4.01/0.98      | m1_pre_topc(X0_54,sK0) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_5141]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5150,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1418,c_5142]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.01/0.98      | ~ m1_pre_topc(X3,X1)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.01/0.98      | ~ v2_pre_topc(X2)
% 4.01/0.98      | ~ v2_pre_topc(X1)
% 4.01/0.98      | v2_struct_0(X1)
% 4.01/0.98      | v2_struct_0(X2)
% 4.01/0.98      | ~ l1_pre_topc(X1)
% 4.01/0.98      | ~ l1_pre_topc(X2)
% 4.01/0.98      | ~ v1_funct_1(X0)
% 4.01/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f48]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_800,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.01/0.98      | ~ m1_pre_topc(X2_54,X0_54)
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ v2_pre_topc(X0_54)
% 4.01/0.98      | ~ v2_pre_topc(X1_54)
% 4.01/0.98      | v2_struct_0(X0_54)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | ~ l1_pre_topc(X0_54)
% 4.01/0.98      | ~ l1_pre_topc(X1_54)
% 4.01/0.98      | ~ v1_funct_1(X0_52)
% 4.01/0.98      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1402,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2518,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54)
% 4.01/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,sK0) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1413,c_1402]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2963,plain,
% 4.01/0.98      ( m1_pre_topc(X0_54,sK0) != iProver_top
% 4.01/0.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54) ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_2518,c_31,c_32,c_33,c_34,c_35,c_36,c_41,c_42]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2964,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54)
% 4.01/0.98      | m1_pre_topc(X0_54,sK0) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_2963]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2972,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1418,c_2964]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5158,plain,
% 4.01/0.98      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_5150,c_2972]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_20,negated_conjecture,
% 4.01/0.98      ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
% 4.01/0.98      inference(cnf_transformation,[],[f69]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_786,negated_conjecture,
% 4.01/0.98      ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.01/0.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 4.01/0.98      | v1_funct_2(k10_tmap_1(X5,X2,X1,X4,X0,X3),u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))
% 4.01/0.98      | ~ m1_pre_topc(X4,X5)
% 4.01/0.98      | ~ m1_pre_topc(X1,X5)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.01/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 4.01/0.98      | ~ v2_pre_topc(X2)
% 4.01/0.98      | ~ v2_pre_topc(X5)
% 4.01/0.98      | v2_struct_0(X5)
% 4.01/0.98      | v2_struct_0(X2)
% 4.01/0.98      | v2_struct_0(X4)
% 4.01/0.98      | v2_struct_0(X1)
% 4.01/0.98      | ~ l1_pre_topc(X5)
% 4.01/0.98      | ~ l1_pre_topc(X2)
% 4.01/0.98      | ~ v1_funct_1(X3)
% 4.01/0.98      | ~ v1_funct_1(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f51]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_797,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.01/0.98      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 4.01/0.98      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54))
% 4.01/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 4.01/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ v2_pre_topc(X3_54)
% 4.01/0.98      | ~ v2_pre_topc(X1_54)
% 4.01/0.98      | v2_struct_0(X0_54)
% 4.01/0.98      | v2_struct_0(X3_54)
% 4.01/0.98      | v2_struct_0(X2_54)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | ~ l1_pre_topc(X3_54)
% 4.01/0.98      | ~ l1_pre_topc(X1_54)
% 4.01/0.98      | ~ v1_funct_1(X0_52)
% 4.01/0.98      | ~ v1_funct_1(X1_52) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1405,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54)) = iProver_top
% 4.01/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X3_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X2_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4733,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),u1_struct_0(sK0),u1_struct_0(X0_54)) = iProver_top
% 4.01/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | v2_struct_0(sK2) = iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_786,c_1405]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_24,negated_conjecture,
% 4.01/0.98      ( ~ v2_struct_0(sK2) ),
% 4.01/0.98      inference(cnf_transformation,[],[f65]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_37,plain,
% 4.01/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_38,plain,
% 4.01/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_22,negated_conjecture,
% 4.01/0.98      ( ~ v2_struct_0(sK3) ),
% 4.01/0.98      inference(cnf_transformation,[],[f67]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_39,plain,
% 4.01/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_21,negated_conjecture,
% 4.01/0.98      ( m1_pre_topc(sK3,sK0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f68]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_40,plain,
% 4.01/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4826,plain,
% 4.01/0.98      ( l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),u1_struct_0(sK0),u1_struct_0(X0_54)) = iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_4733,c_31,c_32,c_33,c_37,c_38,c_39,c_40]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4827,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),u1_struct_0(sK0),u1_struct_0(X0_54)) = iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_4826]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_13,plain,
% 4.01/0.98      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),X4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)))
% 4.01/0.98      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
% 4.01/0.98      | ~ m1_pre_topc(X2,X0)
% 4.01/0.98      | ~ m1_pre_topc(X1,X0)
% 4.01/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
% 4.01/0.98      | ~ v2_pre_topc(X3)
% 4.01/0.98      | ~ v2_pre_topc(X0)
% 4.01/0.98      | v2_struct_0(X0)
% 4.01/0.98      | v2_struct_0(X3)
% 4.01/0.98      | v2_struct_0(X2)
% 4.01/0.98      | v2_struct_0(X1)
% 4.01/0.98      | ~ l1_pre_topc(X0)
% 4.01/0.98      | ~ l1_pre_topc(X3)
% 4.01/0.98      | ~ v1_funct_1(X4) ),
% 4.01/0.98      inference(cnf_transformation,[],[f56]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_792,plain,
% 4.01/0.98      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54),X0_52,k10_tmap_1(X0_54,X3_54,X1_54,X2_54,k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X1_54,X0_52),k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X2_54,X0_52)))
% 4.01/0.98      | ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))
% 4.01/0.98      | ~ m1_pre_topc(X2_54,X0_54)
% 4.01/0.98      | ~ m1_pre_topc(X1_54,X0_54)
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))))
% 4.01/0.98      | ~ v2_pre_topc(X3_54)
% 4.01/0.98      | ~ v2_pre_topc(X0_54)
% 4.01/0.98      | v2_struct_0(X0_54)
% 4.01/0.98      | v2_struct_0(X3_54)
% 4.01/0.98      | v2_struct_0(X2_54)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | ~ l1_pre_topc(X0_54)
% 4.01/0.98      | ~ l1_pre_topc(X3_54)
% 4.01/0.98      | ~ v1_funct_1(X0_52) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1410,plain,
% 4.01/0.98      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54),X0_52,k10_tmap_1(X0_54,X3_54,X1_54,X2_54,k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X1_54,X0_52),k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X2_54,X0_52))) = iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X3_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X2_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3742,plain,
% 4.01/0.98      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | v2_struct_0(sK2) = iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_786,c_1410]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3745,plain,
% 4.01/0.98      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | v2_struct_0(sK2) = iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_3742,c_786]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3750,plain,
% 4.01/0.98      ( l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_3745,c_31,c_32,c_33,c_37,c_38,c_39,c_40]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3751,plain,
% 4.01/0.98      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_3750]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.01/0.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 4.01/0.98      | ~ m1_pre_topc(X4,X5)
% 4.01/0.98      | ~ m1_pre_topc(X1,X5)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.01/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 4.01/0.98      | m1_subset_1(k10_tmap_1(X5,X2,X1,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))))
% 4.01/0.98      | ~ v2_pre_topc(X2)
% 4.01/0.98      | ~ v2_pre_topc(X5)
% 4.01/0.98      | v2_struct_0(X5)
% 4.01/0.98      | v2_struct_0(X2)
% 4.01/0.98      | v2_struct_0(X4)
% 4.01/0.98      | v2_struct_0(X1)
% 4.01/0.98      | ~ l1_pre_topc(X5)
% 4.01/0.98      | ~ l1_pre_topc(X2)
% 4.01/0.98      | ~ v1_funct_1(X3)
% 4.01/0.98      | ~ v1_funct_1(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f52]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_798,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.01/0.98      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 4.01/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 4.01/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 4.01/0.98      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ v2_pre_topc(X3_54)
% 4.01/0.98      | ~ v2_pre_topc(X1_54)
% 4.01/0.98      | v2_struct_0(X0_54)
% 4.01/0.98      | v2_struct_0(X3_54)
% 4.01/0.98      | v2_struct_0(X2_54)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | ~ l1_pre_topc(X3_54)
% 4.01/0.98      | ~ l1_pre_topc(X1_54)
% 4.01/0.98      | ~ v1_funct_1(X0_52)
% 4.01/0.98      | ~ v1_funct_1(X1_52) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1404,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54)))) = iProver_top
% 4.01/0.98      | v2_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X3_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X2_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3249,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) = iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | v2_struct_0(sK2) = iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_786,c_1404]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3842,plain,
% 4.01/0.98      ( l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | m1_subset_1(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) = iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_3249,c_31,c_32,c_33,c_37,c_38,c_39,c_40]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3843,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) = iProver_top
% 4.01/0.98      | v2_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X0_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_3842]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1,plain,
% 4.01/0.98      ( ~ r2_funct_2(X0,X1,X2,X3)
% 4.01/0.98      | ~ v1_funct_2(X3,X0,X1)
% 4.01/0.98      | ~ v1_funct_2(X2,X0,X1)
% 4.01/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.01/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.01/0.98      | ~ v1_funct_1(X3)
% 4.01/0.98      | ~ v1_funct_1(X2)
% 4.01/0.98      | X2 = X3 ),
% 4.01/0.98      inference(cnf_transformation,[],[f43]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_801,plain,
% 4.01/0.98      ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
% 4.01/0.98      | ~ v1_funct_2(X1_52,X0_53,X1_53)
% 4.01/0.98      | ~ v1_funct_2(X0_52,X0_53,X1_53)
% 4.01/0.98      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 4.01/0.98      | ~ v1_funct_1(X0_52)
% 4.01/0.98      | ~ v1_funct_1(X1_52)
% 4.01/0.98      | X0_52 = X1_52 ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1401,plain,
% 4.01/0.98      ( X0_52 = X1_52
% 4.01/0.98      | r2_funct_2(X0_53,X1_53,X0_52,X1_52) != iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,X0_53,X1_53) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2456,plain,
% 4.01/0.98      ( sK4 = X0_52
% 4.01/0.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1413,c_1401]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2918,plain,
% 4.01/0.98      ( v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | sK4 = X0_52
% 4.01/0.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_2456,c_41,c_42]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2919,plain,
% 4.01/0.98      ( sK4 = X0_52
% 4.01/0.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_2918]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3863,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52) = sK4
% 4.01/0.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_3843,c_2919]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4428,plain,
% 4.01/0.98      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top
% 4.01/0.98      | k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52) = sK4
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_3863,c_34,c_35,c_36]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4429,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52) = sK4
% 4.01/0.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top
% 4.01/0.98      | v1_funct_2(X1_52,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(X1_52) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_4428]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4444,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_3751,c_4429]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_43,plain,
% 4.01/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5422,plain,
% 4.01/0.98      ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_4444,c_34,c_35,c_36,c_41,c_42,c_43]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5423,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_5422]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5435,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_4827,c_5423]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5529,plain,
% 4.01/0.98      ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_5435,c_34,c_35,c_36]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5530,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_5529]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5683,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 4.01/0.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 4.01/0.98      inference(demodulation,[status(thm)],[c_5158,c_5530]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_46,plain,
% 4.01/0.98      ( m1_pre_topc(X0,X0) = iProver_top
% 4.01/0.98      | l1_pre_topc(X0) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_48,plain,
% 4.01/0.98      ( m1_pre_topc(sK0,sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_46]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.01/0.98      | ~ m1_pre_topc(X3,X4)
% 4.01/0.98      | ~ m1_pre_topc(X1,X4)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.01/0.98      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 4.01/0.98      | ~ v2_pre_topc(X2)
% 4.01/0.98      | ~ v2_pre_topc(X4)
% 4.01/0.98      | v2_struct_0(X4)
% 4.01/0.98      | v2_struct_0(X2)
% 4.01/0.98      | ~ l1_pre_topc(X4)
% 4.01/0.98      | ~ l1_pre_topc(X2)
% 4.01/0.98      | ~ v1_funct_1(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f55]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_795,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.01/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 4.01/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.01/0.98      | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ v2_pre_topc(X3_54)
% 4.01/0.98      | ~ v2_pre_topc(X1_54)
% 4.01/0.98      | v2_struct_0(X3_54)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | ~ l1_pre_topc(X3_54)
% 4.01/0.98      | ~ l1_pre_topc(X1_54)
% 4.01/0.98      | ~ v1_funct_1(X0_52) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1407,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
% 4.01/0.98      | v2_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X3_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5720,plain,
% 4.01/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 4.01/0.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 4.01/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_5158,c_1407]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_11,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.01/0.98      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 4.01/0.98      | ~ m1_pre_topc(X4,X3)
% 4.01/0.98      | ~ m1_pre_topc(X1,X3)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.01/0.98      | ~ v2_pre_topc(X2)
% 4.01/0.98      | ~ v2_pre_topc(X3)
% 4.01/0.98      | v2_struct_0(X3)
% 4.01/0.98      | v2_struct_0(X2)
% 4.01/0.98      | ~ l1_pre_topc(X3)
% 4.01/0.98      | ~ l1_pre_topc(X2)
% 4.01/0.98      | ~ v1_funct_1(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f54]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_794,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.01/0.98      | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_52),u1_struct_0(X3_54),u1_struct_0(X1_54))
% 4.01/0.98      | ~ m1_pre_topc(X3_54,X2_54)
% 4.01/0.98      | ~ m1_pre_topc(X0_54,X2_54)
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ v2_pre_topc(X2_54)
% 4.01/0.98      | ~ v2_pre_topc(X1_54)
% 4.01/0.98      | v2_struct_0(X2_54)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | ~ l1_pre_topc(X2_54)
% 4.01/0.98      | ~ l1_pre_topc(X1_54)
% 4.01/0.98      | ~ v1_funct_1(X0_52) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1408,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_52),u1_struct_0(X3_54),u1_struct_0(X1_54)) = iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X2_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X2_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X2_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5721,plain,
% 4.01/0.98      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 4.01/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 4.01/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_5158,c_1408]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_12,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.01/0.98      | ~ m1_pre_topc(X3,X4)
% 4.01/0.98      | ~ m1_pre_topc(X1,X4)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.01/0.98      | ~ v2_pre_topc(X2)
% 4.01/0.98      | ~ v2_pre_topc(X4)
% 4.01/0.98      | v2_struct_0(X4)
% 4.01/0.98      | v2_struct_0(X2)
% 4.01/0.98      | ~ l1_pre_topc(X4)
% 4.01/0.98      | ~ l1_pre_topc(X2)
% 4.01/0.98      | ~ v1_funct_1(X0)
% 4.01/0.98      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 4.01/0.98      inference(cnf_transformation,[],[f53]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_793,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.01/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 4.01/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ v2_pre_topc(X3_54)
% 4.01/0.98      | ~ v2_pre_topc(X1_54)
% 4.01/0.98      | v2_struct_0(X3_54)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | ~ l1_pre_topc(X3_54)
% 4.01/0.98      | ~ l1_pre_topc(X1_54)
% 4.01/0.98      | ~ v1_funct_1(X0_52)
% 4.01/0.98      | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1409,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X3_54) = iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X3_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2535,plain,
% 4.01/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,X1_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)) = iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1413,c_1409]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1874,plain,
% 4.01/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 4.01/0.98      | ~ m1_pre_topc(X0_54,X1_54)
% 4.01/0.98      | ~ m1_pre_topc(sK0,X1_54)
% 4.01/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 4.01/0.98      | ~ v2_pre_topc(X1_54)
% 4.01/0.98      | ~ v2_pre_topc(sK1)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | v2_struct_0(sK1)
% 4.01/0.98      | ~ l1_pre_topc(X1_54)
% 4.01/0.98      | ~ l1_pre_topc(sK1)
% 4.01/0.98      | v1_funct_1(k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4))
% 4.01/0.98      | ~ v1_funct_1(sK4) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_793]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1875,plain,
% 4.01/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,X1_54) != iProver_top
% 4.01/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)) = iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_1874]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3110,plain,
% 4.01/0.98      ( v1_funct_1(k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)) = iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,X1_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_2535,c_34,c_35,c_36,c_41,c_42,c_43,c_1875]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3111,plain,
% 4.01/0.98      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,X1_54) != iProver_top
% 4.01/0.98      | v2_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v2_struct_0(X1_54) = iProver_top
% 4.01/0.98      | l1_pre_topc(X1_54) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)) = iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_3110]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5722,plain,
% 4.01/0.98      ( m1_pre_topc(sK2,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_5158,c_3111]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6716,plain,
% 4.01/0.98      ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_5683,c_31,c_32,c_33,c_34,c_35,c_36,c_38,c_41,c_42,
% 4.01/0.98                 c_43,c_48,c_5720,c_5721,c_5722]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6717,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 4.01/0.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 4.01/0.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_6716]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_785,negated_conjecture,
% 4.01/0.98      ( m1_pre_topc(sK3,sK0) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1416,plain,
% 4.01/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5149,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1416,c_5142]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2971,plain,
% 4.01/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1416,c_2964]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5161,plain,
% 4.01/0.98      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_5149,c_2971]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6720,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
% 4.01/0.98      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 4.01/0.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_6717,c_5161]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.01/0.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 4.01/0.98      | ~ m1_pre_topc(X4,X5)
% 4.01/0.98      | ~ m1_pre_topc(X1,X5)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.01/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 4.01/0.98      | ~ v2_pre_topc(X2)
% 4.01/0.98      | ~ v2_pre_topc(X5)
% 4.01/0.98      | v2_struct_0(X5)
% 4.01/0.98      | v2_struct_0(X2)
% 4.01/0.98      | v2_struct_0(X4)
% 4.01/0.98      | v2_struct_0(X1)
% 4.01/0.98      | ~ l1_pre_topc(X5)
% 4.01/0.98      | ~ l1_pre_topc(X2)
% 4.01/0.98      | ~ v1_funct_1(X3)
% 4.01/0.98      | ~ v1_funct_1(X0)
% 4.01/0.98      | v1_funct_1(k10_tmap_1(X5,X2,X1,X4,X0,X3)) ),
% 4.01/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_796,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 4.01/0.98      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 4.01/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 4.01/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 4.01/0.98      | ~ v2_pre_topc(X3_54)
% 4.01/0.98      | ~ v2_pre_topc(X1_54)
% 4.01/0.98      | v2_struct_0(X0_54)
% 4.01/0.98      | v2_struct_0(X3_54)
% 4.01/0.98      | v2_struct_0(X2_54)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | ~ l1_pre_topc(X3_54)
% 4.01/0.98      | ~ l1_pre_topc(X1_54)
% 4.01/0.98      | ~ v1_funct_1(X0_52)
% 4.01/0.98      | ~ v1_funct_1(X1_52)
% 4.01/0.98      | v1_funct_1(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52)) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2122,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK1))
% 4.01/0.98      | ~ v1_funct_2(X1_52,u1_struct_0(X1_54),u1_struct_0(sK1))
% 4.01/0.98      | ~ m1_pre_topc(X1_54,X2_54)
% 4.01/0.98      | ~ m1_pre_topc(X0_54,X2_54)
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1))))
% 4.01/0.98      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK1))))
% 4.01/0.98      | ~ v2_pre_topc(X2_54)
% 4.01/0.98      | ~ v2_pre_topc(sK1)
% 4.01/0.98      | v2_struct_0(X0_54)
% 4.01/0.98      | v2_struct_0(X2_54)
% 4.01/0.98      | v2_struct_0(X1_54)
% 4.01/0.98      | v2_struct_0(sK1)
% 4.01/0.98      | ~ l1_pre_topc(X2_54)
% 4.01/0.98      | ~ l1_pre_topc(sK1)
% 4.01/0.98      | ~ v1_funct_1(X0_52)
% 4.01/0.98      | ~ v1_funct_1(X1_52)
% 4.01/0.98      | v1_funct_1(k10_tmap_1(X2_54,sK1,X0_54,X1_54,X0_52,X1_52)) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_796]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2539,plain,
% 4.01/0.98      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 4.01/0.98      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 4.01/0.98      | ~ m1_pre_topc(sK3,sK0)
% 4.01/0.98      | ~ m1_pre_topc(sK2,sK0)
% 4.01/0.98      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 4.01/0.98      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 4.01/0.98      | ~ v2_pre_topc(sK1)
% 4.01/0.98      | ~ v2_pre_topc(sK0)
% 4.01/0.98      | v2_struct_0(sK3)
% 4.01/0.98      | v2_struct_0(sK2)
% 4.01/0.98      | v2_struct_0(sK1)
% 4.01/0.98      | v2_struct_0(sK0)
% 4.01/0.98      | ~ l1_pre_topc(sK1)
% 4.01/0.98      | ~ l1_pre_topc(sK0)
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 4.01/0.98      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 4.01/0.98      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_2122]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2540,plain,
% 4.01/0.98      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.01/0.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(sK3) = iProver_top
% 4.01/0.98      | v2_struct_0(sK2) = iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 4.01/0.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 4.01/0.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_2539]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6529,plain,
% 4.01/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 4.01/0.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 4.01/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_5161,c_1407]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6530,plain,
% 4.01/0.98      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 4.01/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 4.01/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(sK1) = iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_5161,c_1408]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6531,plain,
% 4.01/0.98      ( m1_pre_topc(sK3,sK0) != iProver_top
% 4.01/0.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 4.01/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v2_struct_0(sK0) = iProver_top
% 4.01/0.98      | l1_pre_topc(sK0) != iProver_top
% 4.01/0.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_5161,c_3111]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6727,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4 ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_6720,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,
% 4.01/0.98                 c_40,c_41,c_42,c_43,c_48,c_2540,c_5720,c_5721,c_5722,
% 4.01/0.98                 c_6529,c_6530,c_6531]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4,plain,
% 4.01/0.98      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 4.01/0.98      | ~ v1_funct_2(X5,X2,X3)
% 4.01/0.98      | ~ v1_funct_2(X4,X0,X1)
% 4.01/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 4.01/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.01/0.98      | v1_xboole_0(X1)
% 4.01/0.98      | v1_xboole_0(X3)
% 4.01/0.98      | ~ v1_funct_1(X5)
% 4.01/0.98      | ~ v1_funct_1(X4) ),
% 4.01/0.98      inference(cnf_transformation,[],[f47]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_16,negated_conjecture,
% 4.01/0.98      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
% 4.01/0.98      inference(cnf_transformation,[],[f73]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_342,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 4.01/0.98      | ~ v1_funct_2(X3,X4,X5)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.01/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.01/0.98      | v1_xboole_0(X2)
% 4.01/0.98      | v1_xboole_0(X5)
% 4.01/0.98      | ~ v1_funct_1(X3)
% 4.01/0.98      | ~ v1_funct_1(X0)
% 4.01/0.98      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0
% 4.01/0.98      | u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) != X4
% 4.01/0.98      | u1_struct_0(sK1) != X5
% 4.01/0.98      | u1_struct_0(sK1) != X2
% 4.01/0.98      | u1_struct_0(sK0) != X1
% 4.01/0.98      | sK4 != X0 ),
% 4.01/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_343,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
% 4.01/0.98      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
% 4.01/0.98      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 4.01/0.98      | v1_xboole_0(u1_struct_0(sK1))
% 4.01/0.98      | ~ v1_funct_1(X0)
% 4.01/0.98      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 4.01/0.98      | sK4 != k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 4.01/0.98      inference(unflattening,[status(thm)],[c_342]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_774,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
% 4.01/0.98      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
% 4.01/0.98      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 4.01/0.98      | v1_xboole_0(u1_struct_0(sK1))
% 4.01/0.98      | ~ v1_funct_1(X0_52)
% 4.01/0.98      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 4.01/0.98      | sK4 != k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_343]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_804,plain,
% 4.01/0.98      ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
% 4.01/0.98      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 4.01/0.98      | v1_xboole_0(u1_struct_0(sK1))
% 4.01/0.98      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 4.01/0.98      | sP0_iProver_split
% 4.01/0.98      | sK4 != k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 4.01/0.98      inference(splitting,
% 4.01/0.98                [splitting(split),new_symbols(definition,[])],
% 4.01/0.98                [c_774]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1427,plain,
% 4.01/0.98      ( sK4 != k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 4.01/0.98      | sP0_iProver_split = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_803,plain,
% 4.01/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
% 4.01/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
% 4.01/0.98      | ~ v1_funct_1(X0_52)
% 4.01/0.98      | ~ sP0_iProver_split ),
% 4.01/0.98      inference(splitting,
% 4.01/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 4.01/0.98                [c_774]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1428,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | sP0_iProver_split != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1485,plain,
% 4.01/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | sP0_iProver_split != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_1428,c_786]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1636,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top ),
% 4.01/0.98      inference(forward_subsumption_resolution,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_1427,c_1485]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_818,plain,
% 4.01/0.98      ( ~ v1_funct_1(X0_52) | v1_funct_1(X1_52) | X1_52 != X0_52 ),
% 4.01/0.98      theory(equality) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1848,plain,
% 4.01/0.98      ( ~ v1_funct_1(X0_52)
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 4.01/0.98      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0_52 ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_818]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1849,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0_52
% 4.01/0.98      | v1_funct_1(X0_52) != iProver_top
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_1848]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1851,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 4.01/0.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 4.01/0.98      | v1_funct_1(sK4) != iProver_top ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_1849]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2289,plain,
% 4.01/0.98      ( v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 4.01/0.98      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4 ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_1636,c_41,c_1851]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2290,plain,
% 4.01/0.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 4.01/0.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_2289]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6730,plain,
% 4.01/0.98      ( sK4 != sK4
% 4.01/0.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 4.01/0.98      inference(demodulation,[status(thm)],[c_6727,c_2290]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6731,plain,
% 4.01/0.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 4.01/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 4.01/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 4.01/0.98      inference(equality_resolution_simp,[status(thm)],[c_6730]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6738,plain,
% 4.01/0.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 4.01/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 4.01/0.98      | v1_xboole_0(u1_struct_0(sK1)) ),
% 4.01/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_6731]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(contradiction,plain,
% 4.01/0.98      ( $false ),
% 4.01/0.98      inference(minisat,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_11041,c_6738,c_17,c_18,c_25,c_27]) ).
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  ------                               Statistics
% 4.01/0.98  
% 4.01/0.98  ------ General
% 4.01/0.98  
% 4.01/0.98  abstr_ref_over_cycles:                  0
% 4.01/0.98  abstr_ref_under_cycles:                 0
% 4.01/0.98  gc_basic_clause_elim:                   0
% 4.01/0.98  forced_gc_time:                         0
% 4.01/0.98  parsing_time:                           0.013
% 4.01/0.98  unif_index_cands_time:                  0.
% 4.01/0.98  unif_index_add_time:                    0.
% 4.01/0.98  orderings_time:                         0.
% 4.01/0.98  out_proof_time:                         0.02
% 4.01/0.98  total_time:                             0.485
% 4.01/0.98  num_of_symbols:                         58
% 4.01/0.98  num_of_terms:                           13816
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing
% 4.01/0.98  
% 4.01/0.98  num_of_splits:                          1
% 4.01/0.98  num_of_split_atoms:                     1
% 4.01/0.98  num_of_reused_defs:                     0
% 4.01/0.98  num_eq_ax_congr_red:                    19
% 4.01/0.98  num_of_sem_filtered_clauses:            1
% 4.01/0.98  num_of_subtypes:                        5
% 4.01/0.98  monotx_restored_types:                  0
% 4.01/0.98  sat_num_of_epr_types:                   0
% 4.01/0.98  sat_num_of_non_cyclic_types:            0
% 4.01/0.98  sat_guarded_non_collapsed_types:        1
% 4.01/0.98  num_pure_diseq_elim:                    0
% 4.01/0.98  simp_replaced_by:                       0
% 4.01/0.98  res_preprocessed:                       169
% 4.01/0.98  prep_upred:                             0
% 4.01/0.98  prep_unflattend:                        21
% 4.01/0.98  smt_new_axioms:                         0
% 4.01/0.98  pred_elim_cands:                        9
% 4.01/0.98  pred_elim:                              2
% 4.01/0.98  pred_elim_cl:                           2
% 4.01/0.98  pred_elim_cycles:                       6
% 4.01/0.98  merged_defs:                            0
% 4.01/0.98  merged_defs_ncl:                        0
% 4.01/0.98  bin_hyper_res:                          0
% 4.01/0.98  prep_cycles:                            4
% 4.01/0.98  pred_elim_time:                         0.013
% 4.01/0.98  splitting_time:                         0.
% 4.01/0.98  sem_filter_time:                        0.
% 4.01/0.98  monotx_time:                            0.
% 4.01/0.98  subtype_inf_time:                       0.001
% 4.01/0.98  
% 4.01/0.98  ------ Problem properties
% 4.01/0.98  
% 4.01/0.98  clauses:                                30
% 4.01/0.98  conjectures:                            14
% 4.01/0.98  epr:                                    13
% 4.01/0.98  horn:                                   20
% 4.01/0.98  ground:                                 15
% 4.01/0.98  unary:                                  14
% 4.01/0.98  binary:                                 1
% 4.01/0.98  lits:                                   171
% 4.01/0.98  lits_eq:                                5
% 4.01/0.98  fd_pure:                                0
% 4.01/0.98  fd_pseudo:                              0
% 4.01/0.98  fd_cond:                                0
% 4.01/0.98  fd_pseudo_cond:                         1
% 4.01/0.98  ac_symbols:                             0
% 4.01/0.98  
% 4.01/0.98  ------ Propositional Solver
% 4.01/0.98  
% 4.01/0.98  prop_solver_calls:                      29
% 4.01/0.98  prop_fast_solver_calls:                 3326
% 4.01/0.98  smt_solver_calls:                       0
% 4.01/0.98  smt_fast_solver_calls:                  0
% 4.01/0.98  prop_num_of_clauses:                    2649
% 4.01/0.98  prop_preprocess_simplified:             7433
% 4.01/0.98  prop_fo_subsumed:                       236
% 4.01/0.98  prop_solver_time:                       0.
% 4.01/0.98  smt_solver_time:                        0.
% 4.01/0.98  smt_fast_solver_time:                   0.
% 4.01/0.98  prop_fast_solver_time:                  0.
% 4.01/0.98  prop_unsat_core_time:                   0.
% 4.01/0.98  
% 4.01/0.98  ------ QBF
% 4.01/0.98  
% 4.01/0.98  qbf_q_res:                              0
% 4.01/0.98  qbf_num_tautologies:                    0
% 4.01/0.98  qbf_prep_cycles:                        0
% 4.01/0.98  
% 4.01/0.98  ------ BMC1
% 4.01/0.98  
% 4.01/0.98  bmc1_current_bound:                     -1
% 4.01/0.98  bmc1_last_solved_bound:                 -1
% 4.01/0.98  bmc1_unsat_core_size:                   -1
% 4.01/0.98  bmc1_unsat_core_parents_size:           -1
% 4.01/0.98  bmc1_merge_next_fun:                    0
% 4.01/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation
% 4.01/0.98  
% 4.01/0.98  inst_num_of_clauses:                    824
% 4.01/0.98  inst_num_in_passive:                    230
% 4.01/0.98  inst_num_in_active:                     510
% 4.01/0.98  inst_num_in_unprocessed:                83
% 4.01/0.98  inst_num_of_loops:                      534
% 4.01/0.98  inst_num_of_learning_restarts:          0
% 4.01/0.98  inst_num_moves_active_passive:          16
% 4.01/0.98  inst_lit_activity:                      0
% 4.01/0.98  inst_lit_activity_moves:                0
% 4.01/0.98  inst_num_tautologies:                   0
% 4.01/0.98  inst_num_prop_implied:                  0
% 4.01/0.98  inst_num_existing_simplified:           0
% 4.01/0.98  inst_num_eq_res_simplified:             0
% 4.01/0.98  inst_num_child_elim:                    0
% 4.01/0.98  inst_num_of_dismatching_blockings:      848
% 4.01/0.98  inst_num_of_non_proper_insts:           1210
% 4.01/0.98  inst_num_of_duplicates:                 0
% 4.01/0.98  inst_inst_num_from_inst_to_res:         0
% 4.01/0.98  inst_dismatching_checking_time:         0.
% 4.01/0.98  
% 4.01/0.98  ------ Resolution
% 4.01/0.98  
% 4.01/0.98  res_num_of_clauses:                     0
% 4.01/0.98  res_num_in_passive:                     0
% 4.01/0.98  res_num_in_active:                      0
% 4.01/0.98  res_num_of_loops:                       173
% 4.01/0.98  res_forward_subset_subsumed:            77
% 4.01/0.98  res_backward_subset_subsumed:           0
% 4.01/0.98  res_forward_subsumed:                   0
% 4.01/0.98  res_backward_subsumed:                  0
% 4.01/0.98  res_forward_subsumption_resolution:     0
% 4.01/0.98  res_backward_subsumption_resolution:    0
% 4.01/0.98  res_clause_to_clause_subsumption:       1132
% 4.01/0.98  res_orphan_elimination:                 0
% 4.01/0.98  res_tautology_del:                      157
% 4.01/0.98  res_num_eq_res_simplified:              0
% 4.01/0.98  res_num_sel_changes:                    0
% 4.01/0.98  res_moves_from_active_to_pass:          0
% 4.01/0.98  
% 4.01/0.98  ------ Superposition
% 4.01/0.98  
% 4.01/0.98  sup_time_total:                         0.
% 4.01/0.98  sup_time_generating:                    0.
% 4.01/0.98  sup_time_sim_full:                      0.
% 4.01/0.98  sup_time_sim_immed:                     0.
% 4.01/0.98  
% 4.01/0.98  sup_num_of_clauses:                     134
% 4.01/0.98  sup_num_in_active:                      98
% 4.01/0.98  sup_num_in_passive:                     36
% 4.01/0.98  sup_num_of_loops:                       106
% 4.01/0.98  sup_fw_superposition:                   78
% 4.01/0.98  sup_bw_superposition:                   75
% 4.01/0.98  sup_immediate_simplified:               47
% 4.01/0.98  sup_given_eliminated:                   0
% 4.01/0.98  comparisons_done:                       0
% 4.01/0.98  comparisons_avoided:                    0
% 4.01/0.98  
% 4.01/0.98  ------ Simplifications
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  sim_fw_subset_subsumed:                 8
% 4.01/0.98  sim_bw_subset_subsumed:                 2
% 4.01/0.98  sim_fw_subsumed:                        20
% 4.01/0.98  sim_bw_subsumed:                        1
% 4.01/0.98  sim_fw_subsumption_res:                 26
% 4.01/0.98  sim_bw_subsumption_res:                 2
% 4.01/0.98  sim_tautology_del:                      1
% 4.01/0.98  sim_eq_tautology_del:                   5
% 4.01/0.98  sim_eq_res_simp:                        1
% 4.01/0.98  sim_fw_demodulated:                     5
% 4.01/0.98  sim_bw_demodulated:                     8
% 4.01/0.98  sim_light_normalised:                   32
% 4.01/0.98  sim_joinable_taut:                      0
% 4.01/0.98  sim_joinable_simp:                      0
% 4.01/0.98  sim_ac_normalised:                      0
% 4.01/0.98  sim_smt_subsumption:                    0
% 4.01/0.98  
%------------------------------------------------------------------------------
