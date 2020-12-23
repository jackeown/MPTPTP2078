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
% DateTime   : Thu Dec  3 12:24:11 EST 2020

% Result     : Theorem 19.29s
% Output     : CNFRefutation 19.29s
% Verified   : 
% Statistics : Number of formulae       :  286 (2985 expanded)
%              Number of clauses        :  184 ( 844 expanded)
%              Number of leaves         :   23 ( 805 expanded)
%              Depth                    :   24
%              Number of atoms          : 1507 (25820 expanded)
%              Number of equality atoms :  425 (1825 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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
             => ( r1_tsep_1(X1,X2)
               => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
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
               => ( r1_tsep_1(X1,X2)
                 => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
          & r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(X0,X1)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5),sK5,k8_tmap_1(X0,X1))
          | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(X0,X1)))
          | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5)) )
        & r1_tsep_1(X1,sK5)
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,sK4)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2),X2,k8_tmap_1(X0,sK4))
              | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,sK4)))
              | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2)) )
            & r1_tsep_1(sK4,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)) )
                & r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK3,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2),X2,k8_tmap_1(sK3,X1))
                | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK3,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK3)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
      | ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4))
      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) )
    & r1_tsep_1(sK4,sK5)
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f61,f76,f75,f74])).

fof(f129,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f77])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f65])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK1(X0,X1,X2)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f66,f67])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f135])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f123,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f106,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f125,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

fof(f126,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f77])).

fof(f127,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f77])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f69])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
        & u1_struct_0(X1) = sK2(X0,X1,X2)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
                    & u1_struct_0(X1) = sK2(X0,X1,X2)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f70,f71])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f131,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f77])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f124,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f117,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f137])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f133,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f77])).

fof(f130,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f77])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f79,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f132,plain,(
    r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f77])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_51,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_6071,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_51])).

cnf(c_7127,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6071])).

cnf(c_10,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_45,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_362,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_45,c_28,c_27,c_26])).

cnf(c_363,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_362])).

cnf(c_6065,plain,
    ( ~ m1_pre_topc(X0_61,X1_61)
    | ~ v2_pre_topc(X1_61)
    | v2_struct_0(X1_61)
    | ~ l1_pre_topc(X1_61)
    | k6_tmap_1(X1_61,u1_struct_0(X0_61)) = k8_tmap_1(X1_61,X0_61) ),
    inference(subtyping,[status(esa)],[c_363])).

cnf(c_7133,plain,
    ( k6_tmap_1(X0_61,u1_struct_0(X1_61)) = k8_tmap_1(X0_61,X1_61)
    | m1_pre_topc(X1_61,X0_61) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6065])).

cnf(c_9306,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7127,c_7133])).

cnf(c_55,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_56,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_54,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_57,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_53,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_58,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_9421,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9306,c_56,c_57,c_58])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6094,plain,
    ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
    | m1_subset_1(k7_tmap_1(X0_61,X0_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,X0_60)))))
    | ~ v2_pre_topc(X0_61)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_7104,plain,
    ( m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
    | m1_subset_1(k7_tmap_1(X0_61,X0_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,X0_60))))) = iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6094])).

cnf(c_10291,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9421,c_7104])).

cnf(c_2267,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_45,c_51])).

cnf(c_2268,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2267])).

cnf(c_2269,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2268])).

cnf(c_10926,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10291,c_56,c_57,c_58,c_2269])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_6104,plain,
    ( ~ v1_funct_2(X0_60,u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)))
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)))))
    | ~ m1_pre_topc(X1_61,X0_61)
    | ~ v2_pre_topc(X0_61)
    | ~ v1_funct_1(X0_60)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61)
    | sK2(X0_61,X1_61,X0_60) = u1_struct_0(X1_61)
    | k9_tmap_1(X0_61,X1_61) = X0_60 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_7094,plain,
    ( sK2(X0_61,X1_61,X0_60) = u1_struct_0(X1_61)
    | k9_tmap_1(X0_61,X1_61) = X0_60
    | v1_funct_2(X0_60,u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61))) != iProver_top
    | m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61))))) != iProver_top
    | m1_pre_topc(X1_61,X0_61) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v1_funct_1(X0_60) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6104])).

cnf(c_11100,plain,
    ( sK2(sK3,sK4,k7_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10926,c_7094])).

cnf(c_60,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_24,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_6093,plain,
    ( v1_funct_2(k7_tmap_1(X0_61,X0_60),u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,X0_60)))
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
    | ~ v2_pre_topc(X0_61)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_7105,plain,
    ( v1_funct_2(k7_tmap_1(X0_61,X0_60),u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,X0_60))) = iProver_top
    | m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6093])).

cnf(c_9759,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9421,c_7105])).

cnf(c_45674,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | sK2(sK3,sK4,k7_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK4)
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11100,c_56,c_57,c_58,c_60,c_2269,c_9759])).

cnf(c_45675,plain,
    ( sK2(sK3,sK4,k7_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK4)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_45674])).

cnf(c_6076,plain,
    ( m1_subset_1(u1_struct_0(X0_61),k1_zfmisc_1(u1_struct_0(X1_61)))
    | ~ m1_pre_topc(X0_61,X1_61)
    | ~ l1_pre_topc(X1_61) ),
    inference(subtyping,[status(esa)],[c_45])).

cnf(c_7122,plain,
    ( m1_subset_1(u1_struct_0(X0_61),k1_zfmisc_1(u1_struct_0(X1_61))) = iProver_top
    | m1_pre_topc(X0_61,X1_61) != iProver_top
    | l1_pre_topc(X1_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6076])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6109,plain,
    ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
    | ~ v2_pre_topc(X0_61)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61)
    | k7_tmap_1(X0_61,X0_60) = k6_partfun1(u1_struct_0(X0_61)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_7089,plain,
    ( k7_tmap_1(X0_61,X0_60) = k6_partfun1(u1_struct_0(X0_61))
    | m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6109])).

cnf(c_8844,plain,
    ( k7_tmap_1(X0_61,u1_struct_0(X1_61)) = k6_partfun1(u1_struct_0(X0_61))
    | m1_pre_topc(X1_61,X0_61) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(superposition,[status(thm)],[c_7122,c_7089])).

cnf(c_11604,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7127,c_8844])).

cnf(c_11784,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11604,c_56,c_57,c_58])).

cnf(c_45678,plain,
    ( sK2(sK3,sK4,k6_partfun1(u1_struct_0(sK3))) = u1_struct_0(sK4)
    | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_45675,c_11784])).

cnf(c_49,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_62,plain,
    ( m1_pre_topc(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_188,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_190,plain,
    ( v2_struct_0(sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_195,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_197,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_31,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2280,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_51])).

cnf(c_2281,plain,
    ( ~ v2_pre_topc(sK3)
    | v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2280])).

cnf(c_2282,plain,
    ( v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2281])).

cnf(c_6073,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(subtyping,[status(esa)],[c_49])).

cnf(c_7125,plain,
    ( m1_pre_topc(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6073])).

cnf(c_11603,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK5)) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7125,c_8844])).

cnf(c_11745,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK5)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11603,c_56,c_57,c_58])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_6092,plain,
    ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
    | ~ v2_pre_topc(X0_61)
    | v1_funct_1(k7_tmap_1(X0_61,X0_60))
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_7106,plain,
    ( m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_61,X0_60)) = iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6092])).

cnf(c_8917,plain,
    ( m1_pre_topc(X0_61,X1_61) != iProver_top
    | v2_pre_topc(X1_61) != iProver_top
    | v1_funct_1(k7_tmap_1(X1_61,u1_struct_0(X0_61))) = iProver_top
    | v2_struct_0(X1_61) = iProver_top
    | l1_pre_topc(X1_61) != iProver_top ),
    inference(superposition,[status(thm)],[c_7122,c_7106])).

cnf(c_11764,plain,
    ( m1_pre_topc(sK5,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11745,c_8917])).

cnf(c_6068,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_54])).

cnf(c_7130,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6068])).

cnf(c_46,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_6075,plain,
    ( m1_pre_topc(X0_61,X0_61)
    | ~ l1_pre_topc(X0_61) ),
    inference(subtyping,[status(esa)],[c_46])).

cnf(c_7123,plain,
    ( m1_pre_topc(X0_61,X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6075])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_6080,plain,
    ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
    | ~ v2_pre_topc(X0_61)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61)
    | u1_struct_0(k6_tmap_1(X0_61,X0_60)) = u1_struct_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_7118,plain,
    ( u1_struct_0(k6_tmap_1(X0_61,X0_60)) = u1_struct_0(X0_61)
    | m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6080])).

cnf(c_9024,plain,
    ( u1_struct_0(k6_tmap_1(X0_61,u1_struct_0(X1_61))) = u1_struct_0(X0_61)
    | m1_pre_topc(X1_61,X0_61) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(superposition,[status(thm)],[c_7122,c_7118])).

cnf(c_12631,plain,
    ( u1_struct_0(k6_tmap_1(X0_61,u1_struct_0(X0_61))) = u1_struct_0(X0_61)
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(superposition,[status(thm)],[c_7123,c_9024])).

cnf(c_12722,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3)
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7130,c_12631])).

cnf(c_9307,plain,
    ( k6_tmap_1(X0_61,u1_struct_0(X0_61)) = k8_tmap_1(X0_61,X0_61)
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(superposition,[status(thm)],[c_7123,c_7133])).

cnf(c_10062,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3)
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7130,c_9307])).

cnf(c_66,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_6274,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_6065])).

cnf(c_10180,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10062,c_55,c_54,c_53,c_66,c_6274])).

cnf(c_12725,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12722,c_10180])).

cnf(c_13149,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12725,c_56,c_58])).

cnf(c_11605,plain,
    ( k7_tmap_1(X0_61,u1_struct_0(X0_61)) = k6_partfun1(u1_struct_0(X0_61))
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(superposition,[status(thm)],[c_7123,c_8844])).

cnf(c_11914,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3))
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7130,c_11605])).

cnf(c_69,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_7227,plain,
    ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0_60) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6109])).

cnf(c_7590,plain,
    ( ~ m1_subset_1(u1_struct_0(X0_61),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(X0_61)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7227])).

cnf(c_7592,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7590])).

cnf(c_11925,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11914,c_55,c_54,c_53,c_66,c_69,c_7592])).

cnf(c_10289,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10180,c_7104])).

cnf(c_65,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_67,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_68,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_70,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_10841,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10289,c_56,c_57,c_58,c_67,c_70])).

cnf(c_11928,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11925,c_10841])).

cnf(c_13151,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13149,c_11928])).

cnf(c_10182,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10180,c_7105])).

cnf(c_10836,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10182,c_56,c_57,c_58,c_67,c_70])).

cnf(c_11929,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11925,c_10836])).

cnf(c_13152,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13149,c_11929])).

cnf(c_12630,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3)
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7127,c_9024])).

cnf(c_12633,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3)
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12630,c_9421])).

cnf(c_13351,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12633,c_56,c_57,c_58])).

cnf(c_29,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_6088,plain,
    ( m1_subset_1(k9_tmap_1(X0_61,X1_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)))))
    | ~ m1_pre_topc(X1_61,X0_61)
    | ~ v2_pre_topc(X0_61)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_7110,plain,
    ( m1_subset_1(k9_tmap_1(X0_61,X1_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61))))) = iProver_top
    | m1_pre_topc(X1_61,X0_61) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6088])).

cnf(c_13403,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13351,c_7110])).

cnf(c_30,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_6087,plain,
    ( v1_funct_2(k9_tmap_1(X0_61,X1_61),u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)))
    | ~ m1_pre_topc(X1_61,X0_61)
    | ~ v2_pre_topc(X0_61)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_7111,plain,
    ( v1_funct_2(k9_tmap_1(X0_61,X1_61),u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61))) = iProver_top
    | m1_pre_topc(X1_61,X0_61) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6087])).

cnf(c_13404,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13351,c_7111])).

cnf(c_14,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_352,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_30,c_29])).

cnf(c_6066,plain,
    ( r1_funct_2(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)),u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,u1_struct_0(X1_61))),k9_tmap_1(X0_61,X1_61),k7_tmap_1(X0_61,u1_struct_0(X1_61)))
    | ~ m1_subset_1(u1_struct_0(X1_61),k1_zfmisc_1(u1_struct_0(X0_61)))
    | ~ m1_pre_topc(X1_61,X0_61)
    | ~ v2_pre_topc(X0_61)
    | ~ v1_funct_1(k9_tmap_1(X0_61,X1_61))
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61) ),
    inference(subtyping,[status(esa)],[c_352])).

cnf(c_7132,plain,
    ( r1_funct_2(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)),u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,u1_struct_0(X1_61))),k9_tmap_1(X0_61,X1_61),k7_tmap_1(X0_61,u1_struct_0(X1_61))) = iProver_top
    | m1_subset_1(u1_struct_0(X1_61),k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
    | m1_pre_topc(X1_61,X0_61) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v1_funct_1(k9_tmap_1(X0_61,X1_61)) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6066])).

cnf(c_13399,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13351,c_7132])).

cnf(c_13410,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),k9_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13399,c_9421,c_11784,c_13351])).

cnf(c_14836,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),k9_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13410,c_56,c_57,c_58,c_60,c_2269,c_2282])).

cnf(c_5,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_6110,plain,
    ( ~ r1_funct_2(X0_60,X1_60,X2_60,X3_60,X4_60,X5_60)
    | ~ v1_funct_2(X5_60,X2_60,X3_60)
    | ~ v1_funct_2(X4_60,X0_60,X1_60)
    | ~ m1_subset_1(X5_60,k1_zfmisc_1(k2_zfmisc_1(X2_60,X3_60)))
    | ~ m1_subset_1(X4_60,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
    | ~ v1_funct_1(X5_60)
    | ~ v1_funct_1(X4_60)
    | v1_xboole_0(X1_60)
    | v1_xboole_0(X3_60)
    | X4_60 = X5_60 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7088,plain,
    ( X0_60 = X1_60
    | r1_funct_2(X2_60,X3_60,X4_60,X5_60,X0_60,X1_60) != iProver_top
    | v1_funct_2(X0_60,X2_60,X3_60) != iProver_top
    | v1_funct_2(X1_60,X4_60,X5_60) != iProver_top
    | m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(X2_60,X3_60))) != iProver_top
    | m1_subset_1(X1_60,k1_zfmisc_1(k2_zfmisc_1(X4_60,X5_60))) != iProver_top
    | v1_funct_1(X0_60) != iProver_top
    | v1_funct_1(X1_60) != iProver_top
    | v1_xboole_0(X5_60) = iProver_top
    | v1_xboole_0(X3_60) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6110])).

cnf(c_14840,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
    | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14836,c_7088])).

cnf(c_45680,plain,
    ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45678,c_56,c_57,c_58,c_60,c_62,c_190,c_197,c_2282,c_11764,c_13151,c_13152,c_13403,c_13404,c_14840])).

cnf(c_42,plain,
    ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
    | ~ r1_xboole_0(u1_struct_0(X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X2,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_47,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_651,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ r1_xboole_0(u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),X0) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | k6_tmap_1(X2,X1) != k8_tmap_1(sK3,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_47])).

cnf(c_652,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ r1_xboole_0(u1_struct_0(sK5),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_pre_topc(sK5,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_656,plain,
    ( v2_struct_0(X1)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(u1_struct_0(sK5),X0)
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_652,c_50])).

cnf(c_657,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ r1_xboole_0(u1_struct_0(sK5),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_pre_topc(sK5,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_656])).

cnf(c_6064,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ r1_xboole_0(u1_struct_0(sK5),X0_60)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_pre_topc(sK5,X0_61)
    | ~ v2_pre_topc(X0_61)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61)
    | k6_tmap_1(X0_61,X0_60) != k8_tmap_1(sK3,sK4)
    | k2_tmap_1(X0_61,k6_tmap_1(X0_61,X0_60),k7_tmap_1(X0_61,X0_60),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_657])).

cnf(c_6116,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),X0_60)
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
    | ~ m1_pre_topc(sK5,X0_61)
    | ~ v2_pre_topc(X0_61)
    | v2_struct_0(X0_61)
    | ~ l1_pre_topc(X0_61)
    | k6_tmap_1(X0_61,X0_60) != k8_tmap_1(sK3,sK4)
    | k2_tmap_1(X0_61,k6_tmap_1(X0_61,X0_60),k7_tmap_1(X0_61,X0_60),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_6064])).

cnf(c_7135,plain,
    ( k6_tmap_1(X0_61,X0_60) != k8_tmap_1(sK3,sK4)
    | k2_tmap_1(X0_61,k6_tmap_1(X0_61,X0_60),k7_tmap_1(X0_61,X0_60),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | r1_xboole_0(u1_struct_0(sK5),X0_60) != iProver_top
    | m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
    | m1_pre_topc(sK5,X0_61) != iProver_top
    | v2_pre_topc(X0_61) != iProver_top
    | v2_struct_0(X0_61) = iProver_top
    | l1_pre_topc(X0_61) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6116])).

cnf(c_9423,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_pre_topc(sK5,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_9421,c_7135])).

cnf(c_9429,plain,
    ( k8_tmap_1(sK3,sK4) != k8_tmap_1(sK3,sK4)
    | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_pre_topc(sK5,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9423,c_9421])).

cnf(c_9430,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_pre_topc(sK5,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9429])).

cnf(c_196,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1697,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_51])).

cnf(c_1698,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1697])).

cnf(c_1708,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_51])).

cnf(c_1709,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1708])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2248,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_49])).

cnf(c_2249,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2248])).

cnf(c_2315,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_51])).

cnf(c_2316,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2315])).

cnf(c_2380,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_51])).

cnf(c_2381,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2380])).

cnf(c_6117,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_6064])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_6098,plain,
    ( ~ v1_funct_2(X0_60,u1_struct_0(X0_61),u1_struct_0(X1_61))
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
    | ~ v1_funct_1(X0_60)
    | v1_funct_1(k2_tmap_1(X0_61,X1_61,X0_60,X2_61))
    | ~ l1_struct_0(X0_61)
    | ~ l1_struct_0(X1_61)
    | ~ l1_struct_0(X2_61) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_7514,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ l1_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6098])).

cnf(c_6115,plain,
    ( ~ l1_pre_topc(X0_61)
    | l1_struct_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_7534,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_6115])).

cnf(c_7537,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_6115])).

cnf(c_7824,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | l1_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6115])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6099,plain,
    ( ~ v1_funct_2(X0_60,u1_struct_0(X0_61),u1_struct_0(X1_61))
    | v1_funct_2(k2_tmap_1(X0_61,X1_61,X0_60,X2_61),u1_struct_0(X2_61),u1_struct_0(X1_61))
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
    | ~ v1_funct_1(X0_60)
    | ~ l1_struct_0(X0_61)
    | ~ l1_struct_0(X1_61)
    | ~ l1_struct_0(X2_61) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_8109,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ l1_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6099])).

cnf(c_48,negated_conjecture,
    ( r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_6074,negated_conjecture,
    ( r1_tsep_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_48])).

cnf(c_7124,plain,
    ( r1_tsep_1(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6074])).

cnf(c_38,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_6082,plain,
    ( ~ r1_tsep_1(X0_61,X1_61)
    | r1_tsep_1(X1_61,X0_61)
    | ~ l1_struct_0(X0_61)
    | ~ l1_struct_0(X1_61) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_7116,plain,
    ( r1_tsep_1(X0_61,X1_61) != iProver_top
    | r1_tsep_1(X1_61,X0_61) = iProver_top
    | l1_struct_0(X0_61) != iProver_top
    | l1_struct_0(X1_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6082])).

cnf(c_8179,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7124,c_7116])).

cnf(c_8180,plain,
    ( r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8179])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6100,plain,
    ( ~ v1_funct_2(X0_60,u1_struct_0(X0_61),u1_struct_0(X1_61))
    | ~ m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
    | m1_subset_1(k2_tmap_1(X0_61,X1_61,X0_60,X2_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61))))
    | ~ v1_funct_1(X0_60)
    | ~ l1_struct_0(X0_61)
    | ~ l1_struct_0(X1_61)
    | ~ l1_struct_0(X2_61) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_8315,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ l1_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6100])).

cnf(c_9432,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK5,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ sP0_iProver_split
    | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9430])).

cnf(c_16,plain,
    ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6101,plain,
    ( r1_xboole_0(u1_struct_0(X0_61),u1_struct_0(X1_61))
    | ~ r1_tsep_1(X0_61,X1_61)
    | ~ l1_struct_0(X0_61)
    | ~ l1_struct_0(X1_61) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_9530,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_6101])).

cnf(c_10059,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9430,c_55,c_54,c_53,c_49,c_196,c_1698,c_1709,c_2249,c_2268,c_2281,c_2316,c_2381,c_6117,c_7514,c_7534,c_7537,c_7824,c_8109,c_8180,c_8315,c_9432,c_9530])).

cnf(c_11787,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
    inference(demodulation,[status(thm)],[c_11784,c_10059])).

cnf(c_45688,plain,
    ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK5) ),
    inference(demodulation,[status(thm)],[c_45680,c_11787])).

cnf(c_45690,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_45688])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:19:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 19.29/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.29/2.98  
% 19.29/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.29/2.98  
% 19.29/2.98  ------  iProver source info
% 19.29/2.98  
% 19.29/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.29/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.29/2.98  git: non_committed_changes: false
% 19.29/2.98  git: last_make_outside_of_git: false
% 19.29/2.98  
% 19.29/2.98  ------ 
% 19.29/2.98  
% 19.29/2.98  ------ Input Options
% 19.29/2.98  
% 19.29/2.98  --out_options                           all
% 19.29/2.98  --tptp_safe_out                         true
% 19.29/2.98  --problem_path                          ""
% 19.29/2.98  --include_path                          ""
% 19.29/2.98  --clausifier                            res/vclausify_rel
% 19.29/2.98  --clausifier_options                    ""
% 19.29/2.98  --stdin                                 false
% 19.29/2.98  --stats_out                             all
% 19.29/2.98  
% 19.29/2.98  ------ General Options
% 19.29/2.98  
% 19.29/2.98  --fof                                   false
% 19.29/2.98  --time_out_real                         305.
% 19.29/2.98  --time_out_virtual                      -1.
% 19.29/2.98  --symbol_type_check                     false
% 19.29/2.98  --clausify_out                          false
% 19.29/2.98  --sig_cnt_out                           false
% 19.29/2.98  --trig_cnt_out                          false
% 19.29/2.98  --trig_cnt_out_tolerance                1.
% 19.29/2.98  --trig_cnt_out_sk_spl                   false
% 19.29/2.98  --abstr_cl_out                          false
% 19.29/2.98  
% 19.29/2.98  ------ Global Options
% 19.29/2.98  
% 19.29/2.98  --schedule                              default
% 19.29/2.98  --add_important_lit                     false
% 19.29/2.98  --prop_solver_per_cl                    1000
% 19.29/2.98  --min_unsat_core                        false
% 19.29/2.98  --soft_assumptions                      false
% 19.29/2.98  --soft_lemma_size                       3
% 19.29/2.98  --prop_impl_unit_size                   0
% 19.29/2.98  --prop_impl_unit                        []
% 19.29/2.98  --share_sel_clauses                     true
% 19.29/2.98  --reset_solvers                         false
% 19.29/2.98  --bc_imp_inh                            [conj_cone]
% 19.29/2.98  --conj_cone_tolerance                   3.
% 19.29/2.98  --extra_neg_conj                        none
% 19.29/2.98  --large_theory_mode                     true
% 19.29/2.98  --prolific_symb_bound                   200
% 19.29/2.98  --lt_threshold                          2000
% 19.29/2.98  --clause_weak_htbl                      true
% 19.29/2.98  --gc_record_bc_elim                     false
% 19.29/2.98  
% 19.29/2.98  ------ Preprocessing Options
% 19.29/2.98  
% 19.29/2.98  --preprocessing_flag                    true
% 19.29/2.98  --time_out_prep_mult                    0.1
% 19.29/2.98  --splitting_mode                        input
% 19.29/2.98  --splitting_grd                         true
% 19.29/2.98  --splitting_cvd                         false
% 19.29/2.98  --splitting_cvd_svl                     false
% 19.29/2.98  --splitting_nvd                         32
% 19.29/2.98  --sub_typing                            true
% 19.29/2.98  --prep_gs_sim                           true
% 19.29/2.98  --prep_unflatten                        true
% 19.29/2.98  --prep_res_sim                          true
% 19.29/2.98  --prep_upred                            true
% 19.29/2.98  --prep_sem_filter                       exhaustive
% 19.29/2.98  --prep_sem_filter_out                   false
% 19.29/2.98  --pred_elim                             true
% 19.29/2.98  --res_sim_input                         true
% 19.29/2.98  --eq_ax_congr_red                       true
% 19.29/2.98  --pure_diseq_elim                       true
% 19.29/2.98  --brand_transform                       false
% 19.29/2.98  --non_eq_to_eq                          false
% 19.29/2.98  --prep_def_merge                        true
% 19.29/2.98  --prep_def_merge_prop_impl              false
% 19.29/2.98  --prep_def_merge_mbd                    true
% 19.29/2.98  --prep_def_merge_tr_red                 false
% 19.29/2.98  --prep_def_merge_tr_cl                  false
% 19.29/2.98  --smt_preprocessing                     true
% 19.29/2.98  --smt_ac_axioms                         fast
% 19.29/2.98  --preprocessed_out                      false
% 19.29/2.98  --preprocessed_stats                    false
% 19.29/2.98  
% 19.29/2.98  ------ Abstraction refinement Options
% 19.29/2.98  
% 19.29/2.98  --abstr_ref                             []
% 19.29/2.98  --abstr_ref_prep                        false
% 19.29/2.98  --abstr_ref_until_sat                   false
% 19.29/2.98  --abstr_ref_sig_restrict                funpre
% 19.29/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.29/2.98  --abstr_ref_under                       []
% 19.29/2.98  
% 19.29/2.98  ------ SAT Options
% 19.29/2.98  
% 19.29/2.98  --sat_mode                              false
% 19.29/2.98  --sat_fm_restart_options                ""
% 19.29/2.98  --sat_gr_def                            false
% 19.29/2.98  --sat_epr_types                         true
% 19.29/2.98  --sat_non_cyclic_types                  false
% 19.29/2.98  --sat_finite_models                     false
% 19.29/2.98  --sat_fm_lemmas                         false
% 19.29/2.98  --sat_fm_prep                           false
% 19.29/2.98  --sat_fm_uc_incr                        true
% 19.29/2.98  --sat_out_model                         small
% 19.29/2.98  --sat_out_clauses                       false
% 19.29/2.98  
% 19.29/2.98  ------ QBF Options
% 19.29/2.98  
% 19.29/2.98  --qbf_mode                              false
% 19.29/2.98  --qbf_elim_univ                         false
% 19.29/2.98  --qbf_dom_inst                          none
% 19.29/2.98  --qbf_dom_pre_inst                      false
% 19.29/2.98  --qbf_sk_in                             false
% 19.29/2.98  --qbf_pred_elim                         true
% 19.29/2.98  --qbf_split                             512
% 19.29/2.98  
% 19.29/2.98  ------ BMC1 Options
% 19.29/2.98  
% 19.29/2.98  --bmc1_incremental                      false
% 19.29/2.98  --bmc1_axioms                           reachable_all
% 19.29/2.98  --bmc1_min_bound                        0
% 19.29/2.98  --bmc1_max_bound                        -1
% 19.29/2.98  --bmc1_max_bound_default                -1
% 19.29/2.98  --bmc1_symbol_reachability              true
% 19.29/2.98  --bmc1_property_lemmas                  false
% 19.29/2.98  --bmc1_k_induction                      false
% 19.29/2.98  --bmc1_non_equiv_states                 false
% 19.29/2.98  --bmc1_deadlock                         false
% 19.29/2.98  --bmc1_ucm                              false
% 19.29/2.98  --bmc1_add_unsat_core                   none
% 19.29/2.98  --bmc1_unsat_core_children              false
% 19.29/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.29/2.98  --bmc1_out_stat                         full
% 19.29/2.98  --bmc1_ground_init                      false
% 19.29/2.98  --bmc1_pre_inst_next_state              false
% 19.29/2.98  --bmc1_pre_inst_state                   false
% 19.29/2.98  --bmc1_pre_inst_reach_state             false
% 19.29/2.98  --bmc1_out_unsat_core                   false
% 19.29/2.98  --bmc1_aig_witness_out                  false
% 19.29/2.98  --bmc1_verbose                          false
% 19.29/2.98  --bmc1_dump_clauses_tptp                false
% 19.29/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.29/2.98  --bmc1_dump_file                        -
% 19.29/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.29/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.29/2.98  --bmc1_ucm_extend_mode                  1
% 19.29/2.98  --bmc1_ucm_init_mode                    2
% 19.29/2.98  --bmc1_ucm_cone_mode                    none
% 19.29/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.29/2.98  --bmc1_ucm_relax_model                  4
% 19.29/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.29/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.29/2.98  --bmc1_ucm_layered_model                none
% 19.29/2.98  --bmc1_ucm_max_lemma_size               10
% 19.29/2.98  
% 19.29/2.98  ------ AIG Options
% 19.29/2.98  
% 19.29/2.98  --aig_mode                              false
% 19.29/2.98  
% 19.29/2.98  ------ Instantiation Options
% 19.29/2.98  
% 19.29/2.98  --instantiation_flag                    true
% 19.29/2.98  --inst_sos_flag                         true
% 19.29/2.98  --inst_sos_phase                        true
% 19.29/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.29/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.29/2.98  --inst_lit_sel_side                     num_symb
% 19.29/2.98  --inst_solver_per_active                1400
% 19.29/2.98  --inst_solver_calls_frac                1.
% 19.29/2.98  --inst_passive_queue_type               priority_queues
% 19.29/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.29/2.98  --inst_passive_queues_freq              [25;2]
% 19.29/2.98  --inst_dismatching                      true
% 19.29/2.98  --inst_eager_unprocessed_to_passive     true
% 19.29/2.98  --inst_prop_sim_given                   true
% 19.29/2.98  --inst_prop_sim_new                     false
% 19.29/2.98  --inst_subs_new                         false
% 19.29/2.98  --inst_eq_res_simp                      false
% 19.29/2.98  --inst_subs_given                       false
% 19.29/2.98  --inst_orphan_elimination               true
% 19.29/2.98  --inst_learning_loop_flag               true
% 19.29/2.98  --inst_learning_start                   3000
% 19.29/2.98  --inst_learning_factor                  2
% 19.29/2.98  --inst_start_prop_sim_after_learn       3
% 19.29/2.98  --inst_sel_renew                        solver
% 19.29/2.98  --inst_lit_activity_flag                true
% 19.29/2.98  --inst_restr_to_given                   false
% 19.29/2.98  --inst_activity_threshold               500
% 19.29/2.98  --inst_out_proof                        true
% 19.29/2.98  
% 19.29/2.98  ------ Resolution Options
% 19.29/2.98  
% 19.29/2.98  --resolution_flag                       true
% 19.29/2.98  --res_lit_sel                           adaptive
% 19.29/2.98  --res_lit_sel_side                      none
% 19.29/2.98  --res_ordering                          kbo
% 19.29/2.98  --res_to_prop_solver                    active
% 19.29/2.98  --res_prop_simpl_new                    false
% 19.29/2.98  --res_prop_simpl_given                  true
% 19.29/2.98  --res_passive_queue_type                priority_queues
% 19.29/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.29/2.98  --res_passive_queues_freq               [15;5]
% 19.29/2.98  --res_forward_subs                      full
% 19.29/2.98  --res_backward_subs                     full
% 19.29/2.98  --res_forward_subs_resolution           true
% 19.29/2.98  --res_backward_subs_resolution          true
% 19.29/2.98  --res_orphan_elimination                true
% 19.29/2.98  --res_time_limit                        2.
% 19.29/2.98  --res_out_proof                         true
% 19.29/2.98  
% 19.29/2.98  ------ Superposition Options
% 19.29/2.98  
% 19.29/2.98  --superposition_flag                    true
% 19.29/2.98  --sup_passive_queue_type                priority_queues
% 19.29/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.29/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.29/2.98  --demod_completeness_check              fast
% 19.29/2.98  --demod_use_ground                      true
% 19.29/2.98  --sup_to_prop_solver                    passive
% 19.29/2.98  --sup_prop_simpl_new                    true
% 19.29/2.98  --sup_prop_simpl_given                  true
% 19.29/2.98  --sup_fun_splitting                     true
% 19.29/2.98  --sup_smt_interval                      50000
% 19.29/2.98  
% 19.29/2.98  ------ Superposition Simplification Setup
% 19.29/2.98  
% 19.29/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.29/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.29/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.29/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.29/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.29/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.29/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.29/2.98  --sup_immed_triv                        [TrivRules]
% 19.29/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/2.98  --sup_immed_bw_main                     []
% 19.29/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.29/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.29/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/2.98  --sup_input_bw                          []
% 19.29/2.98  
% 19.29/2.98  ------ Combination Options
% 19.29/2.98  
% 19.29/2.98  --comb_res_mult                         3
% 19.29/2.98  --comb_sup_mult                         2
% 19.29/2.98  --comb_inst_mult                        10
% 19.29/2.98  
% 19.29/2.98  ------ Debug Options
% 19.29/2.98  
% 19.29/2.98  --dbg_backtrace                         false
% 19.29/2.98  --dbg_dump_prop_clauses                 false
% 19.29/2.98  --dbg_dump_prop_clauses_file            -
% 19.29/2.98  --dbg_out_stat                          false
% 19.29/2.98  ------ Parsing...
% 19.29/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.29/2.98  
% 19.29/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.29/2.98  
% 19.29/2.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.29/2.98  
% 19.29/2.98  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.29/2.98  ------ Proving...
% 19.29/2.98  ------ Problem Properties 
% 19.29/2.98  
% 19.29/2.98  
% 19.29/2.98  clauses                                 54
% 19.29/2.98  conjectures                             8
% 19.29/2.98  EPR                                     12
% 19.29/2.98  Horn                                    24
% 19.29/2.98  unary                                   8
% 19.29/2.98  binary                                  3
% 19.29/2.98  lits                                    271
% 19.29/2.98  lits eq                                 18
% 19.29/2.98  fd_pure                                 0
% 19.29/2.98  fd_pseudo                               0
% 19.29/2.98  fd_cond                                 0
% 19.29/2.98  fd_pseudo_cond                          7
% 19.29/2.98  AC symbols                              0
% 19.29/2.98  
% 19.29/2.98  ------ Schedule dynamic 5 is on 
% 19.29/2.98  
% 19.29/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.29/2.98  
% 19.29/2.98  
% 19.29/2.98  ------ 
% 19.29/2.98  Current options:
% 19.29/2.98  ------ 
% 19.29/2.98  
% 19.29/2.98  ------ Input Options
% 19.29/2.98  
% 19.29/2.98  --out_options                           all
% 19.29/2.98  --tptp_safe_out                         true
% 19.29/2.98  --problem_path                          ""
% 19.29/2.98  --include_path                          ""
% 19.29/2.98  --clausifier                            res/vclausify_rel
% 19.29/2.98  --clausifier_options                    ""
% 19.29/2.98  --stdin                                 false
% 19.29/2.98  --stats_out                             all
% 19.29/2.98  
% 19.29/2.98  ------ General Options
% 19.29/2.98  
% 19.29/2.98  --fof                                   false
% 19.29/2.98  --time_out_real                         305.
% 19.29/2.98  --time_out_virtual                      -1.
% 19.29/2.98  --symbol_type_check                     false
% 19.29/2.98  --clausify_out                          false
% 19.29/2.98  --sig_cnt_out                           false
% 19.29/2.98  --trig_cnt_out                          false
% 19.29/2.98  --trig_cnt_out_tolerance                1.
% 19.29/2.98  --trig_cnt_out_sk_spl                   false
% 19.29/2.98  --abstr_cl_out                          false
% 19.29/2.98  
% 19.29/2.98  ------ Global Options
% 19.29/2.98  
% 19.29/2.98  --schedule                              default
% 19.29/2.98  --add_important_lit                     false
% 19.29/2.98  --prop_solver_per_cl                    1000
% 19.29/2.98  --min_unsat_core                        false
% 19.29/2.98  --soft_assumptions                      false
% 19.29/2.98  --soft_lemma_size                       3
% 19.29/2.98  --prop_impl_unit_size                   0
% 19.29/2.98  --prop_impl_unit                        []
% 19.29/2.98  --share_sel_clauses                     true
% 19.29/2.98  --reset_solvers                         false
% 19.29/2.98  --bc_imp_inh                            [conj_cone]
% 19.29/2.98  --conj_cone_tolerance                   3.
% 19.29/2.98  --extra_neg_conj                        none
% 19.29/2.98  --large_theory_mode                     true
% 19.29/2.98  --prolific_symb_bound                   200
% 19.29/2.98  --lt_threshold                          2000
% 19.29/2.98  --clause_weak_htbl                      true
% 19.29/2.98  --gc_record_bc_elim                     false
% 19.29/2.98  
% 19.29/2.98  ------ Preprocessing Options
% 19.29/2.98  
% 19.29/2.98  --preprocessing_flag                    true
% 19.29/2.98  --time_out_prep_mult                    0.1
% 19.29/2.98  --splitting_mode                        input
% 19.29/2.98  --splitting_grd                         true
% 19.29/2.98  --splitting_cvd                         false
% 19.29/2.98  --splitting_cvd_svl                     false
% 19.29/2.98  --splitting_nvd                         32
% 19.29/2.98  --sub_typing                            true
% 19.29/2.98  --prep_gs_sim                           true
% 19.29/2.98  --prep_unflatten                        true
% 19.29/2.98  --prep_res_sim                          true
% 19.29/2.98  --prep_upred                            true
% 19.29/2.98  --prep_sem_filter                       exhaustive
% 19.29/2.98  --prep_sem_filter_out                   false
% 19.29/2.98  --pred_elim                             true
% 19.29/2.98  --res_sim_input                         true
% 19.29/2.98  --eq_ax_congr_red                       true
% 19.29/2.98  --pure_diseq_elim                       true
% 19.29/2.98  --brand_transform                       false
% 19.29/2.98  --non_eq_to_eq                          false
% 19.29/2.98  --prep_def_merge                        true
% 19.29/2.98  --prep_def_merge_prop_impl              false
% 19.29/2.98  --prep_def_merge_mbd                    true
% 19.29/2.98  --prep_def_merge_tr_red                 false
% 19.29/2.98  --prep_def_merge_tr_cl                  false
% 19.29/2.98  --smt_preprocessing                     true
% 19.29/2.98  --smt_ac_axioms                         fast
% 19.29/2.98  --preprocessed_out                      false
% 19.29/2.98  --preprocessed_stats                    false
% 19.29/2.98  
% 19.29/2.98  ------ Abstraction refinement Options
% 19.29/2.98  
% 19.29/2.98  --abstr_ref                             []
% 19.29/2.98  --abstr_ref_prep                        false
% 19.29/2.98  --abstr_ref_until_sat                   false
% 19.29/2.98  --abstr_ref_sig_restrict                funpre
% 19.29/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.29/2.98  --abstr_ref_under                       []
% 19.29/2.98  
% 19.29/2.98  ------ SAT Options
% 19.29/2.98  
% 19.29/2.98  --sat_mode                              false
% 19.29/2.98  --sat_fm_restart_options                ""
% 19.29/2.98  --sat_gr_def                            false
% 19.29/2.98  --sat_epr_types                         true
% 19.29/2.98  --sat_non_cyclic_types                  false
% 19.29/2.98  --sat_finite_models                     false
% 19.29/2.98  --sat_fm_lemmas                         false
% 19.29/2.98  --sat_fm_prep                           false
% 19.29/2.98  --sat_fm_uc_incr                        true
% 19.29/2.98  --sat_out_model                         small
% 19.29/2.98  --sat_out_clauses                       false
% 19.29/2.98  
% 19.29/2.98  ------ QBF Options
% 19.29/2.98  
% 19.29/2.98  --qbf_mode                              false
% 19.29/2.98  --qbf_elim_univ                         false
% 19.29/2.98  --qbf_dom_inst                          none
% 19.29/2.98  --qbf_dom_pre_inst                      false
% 19.29/2.98  --qbf_sk_in                             false
% 19.29/2.98  --qbf_pred_elim                         true
% 19.29/2.98  --qbf_split                             512
% 19.29/2.98  
% 19.29/2.98  ------ BMC1 Options
% 19.29/2.98  
% 19.29/2.98  --bmc1_incremental                      false
% 19.29/2.98  --bmc1_axioms                           reachable_all
% 19.29/2.98  --bmc1_min_bound                        0
% 19.29/2.98  --bmc1_max_bound                        -1
% 19.29/2.98  --bmc1_max_bound_default                -1
% 19.29/2.98  --bmc1_symbol_reachability              true
% 19.29/2.98  --bmc1_property_lemmas                  false
% 19.29/2.98  --bmc1_k_induction                      false
% 19.29/2.98  --bmc1_non_equiv_states                 false
% 19.29/2.98  --bmc1_deadlock                         false
% 19.29/2.98  --bmc1_ucm                              false
% 19.29/2.98  --bmc1_add_unsat_core                   none
% 19.29/2.98  --bmc1_unsat_core_children              false
% 19.29/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.29/2.98  --bmc1_out_stat                         full
% 19.29/2.98  --bmc1_ground_init                      false
% 19.29/2.98  --bmc1_pre_inst_next_state              false
% 19.29/2.98  --bmc1_pre_inst_state                   false
% 19.29/2.98  --bmc1_pre_inst_reach_state             false
% 19.29/2.98  --bmc1_out_unsat_core                   false
% 19.29/2.98  --bmc1_aig_witness_out                  false
% 19.29/2.98  --bmc1_verbose                          false
% 19.29/2.98  --bmc1_dump_clauses_tptp                false
% 19.29/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.29/2.98  --bmc1_dump_file                        -
% 19.29/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.29/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.29/2.98  --bmc1_ucm_extend_mode                  1
% 19.29/2.98  --bmc1_ucm_init_mode                    2
% 19.29/2.98  --bmc1_ucm_cone_mode                    none
% 19.29/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.29/2.98  --bmc1_ucm_relax_model                  4
% 19.29/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.29/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.29/2.98  --bmc1_ucm_layered_model                none
% 19.29/2.98  --bmc1_ucm_max_lemma_size               10
% 19.29/2.98  
% 19.29/2.98  ------ AIG Options
% 19.29/2.98  
% 19.29/2.98  --aig_mode                              false
% 19.29/2.98  
% 19.29/2.98  ------ Instantiation Options
% 19.29/2.98  
% 19.29/2.98  --instantiation_flag                    true
% 19.29/2.98  --inst_sos_flag                         true
% 19.29/2.98  --inst_sos_phase                        true
% 19.29/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.29/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.29/2.98  --inst_lit_sel_side                     none
% 19.29/2.98  --inst_solver_per_active                1400
% 19.29/2.98  --inst_solver_calls_frac                1.
% 19.29/2.98  --inst_passive_queue_type               priority_queues
% 19.29/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.29/2.98  --inst_passive_queues_freq              [25;2]
% 19.29/2.98  --inst_dismatching                      true
% 19.29/2.98  --inst_eager_unprocessed_to_passive     true
% 19.29/2.98  --inst_prop_sim_given                   true
% 19.29/2.98  --inst_prop_sim_new                     false
% 19.29/2.98  --inst_subs_new                         false
% 19.29/2.98  --inst_eq_res_simp                      false
% 19.29/2.98  --inst_subs_given                       false
% 19.29/2.98  --inst_orphan_elimination               true
% 19.29/2.98  --inst_learning_loop_flag               true
% 19.29/2.98  --inst_learning_start                   3000
% 19.29/2.98  --inst_learning_factor                  2
% 19.29/2.98  --inst_start_prop_sim_after_learn       3
% 19.29/2.98  --inst_sel_renew                        solver
% 19.29/2.98  --inst_lit_activity_flag                true
% 19.29/2.98  --inst_restr_to_given                   false
% 19.29/2.98  --inst_activity_threshold               500
% 19.29/2.98  --inst_out_proof                        true
% 19.29/2.98  
% 19.29/2.98  ------ Resolution Options
% 19.29/2.98  
% 19.29/2.98  --resolution_flag                       false
% 19.29/2.98  --res_lit_sel                           adaptive
% 19.29/2.98  --res_lit_sel_side                      none
% 19.29/2.98  --res_ordering                          kbo
% 19.29/2.98  --res_to_prop_solver                    active
% 19.29/2.98  --res_prop_simpl_new                    false
% 19.29/2.98  --res_prop_simpl_given                  true
% 19.29/2.98  --res_passive_queue_type                priority_queues
% 19.29/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.29/2.98  --res_passive_queues_freq               [15;5]
% 19.29/2.98  --res_forward_subs                      full
% 19.29/2.98  --res_backward_subs                     full
% 19.29/2.98  --res_forward_subs_resolution           true
% 19.29/2.98  --res_backward_subs_resolution          true
% 19.29/2.98  --res_orphan_elimination                true
% 19.29/2.98  --res_time_limit                        2.
% 19.29/2.98  --res_out_proof                         true
% 19.29/2.98  
% 19.29/2.98  ------ Superposition Options
% 19.29/2.98  
% 19.29/2.98  --superposition_flag                    true
% 19.29/2.98  --sup_passive_queue_type                priority_queues
% 19.29/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.29/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.29/2.98  --demod_completeness_check              fast
% 19.29/2.98  --demod_use_ground                      true
% 19.29/2.98  --sup_to_prop_solver                    passive
% 19.29/2.98  --sup_prop_simpl_new                    true
% 19.29/2.98  --sup_prop_simpl_given                  true
% 19.29/2.98  --sup_fun_splitting                     true
% 19.29/2.98  --sup_smt_interval                      50000
% 19.29/2.98  
% 19.29/2.98  ------ Superposition Simplification Setup
% 19.29/2.98  
% 19.29/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.29/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.29/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.29/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.29/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.29/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.29/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.29/2.98  --sup_immed_triv                        [TrivRules]
% 19.29/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/2.98  --sup_immed_bw_main                     []
% 19.29/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.29/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.29/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/2.98  --sup_input_bw                          []
% 19.29/2.98  
% 19.29/2.98  ------ Combination Options
% 19.29/2.98  
% 19.29/2.98  --comb_res_mult                         3
% 19.29/2.98  --comb_sup_mult                         2
% 19.29/2.98  --comb_inst_mult                        10
% 19.29/2.98  
% 19.29/2.98  ------ Debug Options
% 19.29/2.98  
% 19.29/2.98  --dbg_backtrace                         false
% 19.29/2.98  --dbg_dump_prop_clauses                 false
% 19.29/2.98  --dbg_dump_prop_clauses_file            -
% 19.29/2.98  --dbg_out_stat                          false
% 19.29/2.98  
% 19.29/2.98  
% 19.29/2.98  
% 19.29/2.98  
% 19.29/2.98  ------ Proving...
% 19.29/2.98  
% 19.29/2.98  
% 19.29/2.98  % SZS status Theorem for theBenchmark.p
% 19.29/2.98  
% 19.29/2.98   Resolution empty clause
% 19.29/2.98  
% 19.29/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.29/2.98  
% 19.29/2.98  fof(f22,conjecture,(
% 19.29/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)))))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f23,negated_conjecture,(
% 19.29/2.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)))))))),
% 19.29/2.98    inference(negated_conjecture,[],[f22])).
% 19.29/2.98  
% 19.29/2.98  fof(f60,plain,(
% 19.29/2.98    ? [X0] : (? [X1] : (? [X2] : (((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f23])).
% 19.29/2.98  
% 19.29/2.98  fof(f61,plain,(
% 19.29/2.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f60])).
% 19.29/2.98  
% 19.29/2.98  fof(f76,plain,(
% 19.29/2.98    ( ! [X0,X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5),sK5,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5))) & r1_tsep_1(X1,sK5) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 19.29/2.98    introduced(choice_axiom,[])).
% 19.29/2.98  
% 19.29/2.98  fof(f75,plain,(
% 19.29/2.98    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,sK4))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2),X2,k8_tmap_1(X0,sK4)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,sK4))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2))) & r1_tsep_1(sK4,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 19.29/2.98    introduced(choice_axiom,[])).
% 19.29/2.98  
% 19.29/2.98  fof(f74,plain,(
% 19.29/2.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK3,X1))))) | ~v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2),X2,k8_tmap_1(sK3,X1)) | ~v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK3,X1))) | ~v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 19.29/2.98    introduced(choice_axiom,[])).
% 19.29/2.98  
% 19.29/2.98  fof(f77,plain,(
% 19.29/2.98    (((~m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))) & r1_tsep_1(sK4,sK5) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 19.29/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f61,f76,f75,f74])).
% 19.29/2.98  
% 19.29/2.98  fof(f129,plain,(
% 19.29/2.98    m1_pre_topc(sK4,sK3)),
% 19.29/2.98    inference(cnf_transformation,[],[f77])).
% 19.29/2.98  
% 19.29/2.98  fof(f7,axiom,(
% 19.29/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f33,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f7])).
% 19.29/2.98  
% 19.29/2.98  fof(f34,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f33])).
% 19.29/2.98  
% 19.29/2.98  fof(f65,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(nnf_transformation,[],[f34])).
% 19.29/2.98  
% 19.29/2.98  fof(f66,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(rectify,[],[f65])).
% 19.29/2.98  
% 19.29/2.98  fof(f67,plain,(
% 19.29/2.98    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.29/2.98    introduced(choice_axiom,[])).
% 19.29/2.98  
% 19.29/2.98  fof(f68,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f66,f67])).
% 19.29/2.98  
% 19.29/2.98  fof(f85,plain,(
% 19.29/2.98    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f68])).
% 19.29/2.98  
% 19.29/2.98  fof(f135,plain,(
% 19.29/2.98    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(equality_resolution,[],[f85])).
% 19.29/2.98  
% 19.29/2.98  fof(f136,plain,(
% 19.29/2.98    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(equality_resolution,[],[f135])).
% 19.29/2.98  
% 19.29/2.98  fof(f20,axiom,(
% 19.29/2.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f58,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.29/2.98    inference(ennf_transformation,[],[f20])).
% 19.29/2.98  
% 19.29/2.98  fof(f123,plain,(
% 19.29/2.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f58])).
% 19.29/2.98  
% 19.29/2.98  fof(f13,axiom,(
% 19.29/2.98    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f44,plain,(
% 19.29/2.98    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f13])).
% 19.29/2.98  
% 19.29/2.98  fof(f45,plain,(
% 19.29/2.98    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f44])).
% 19.29/2.98  
% 19.29/2.98  fof(f104,plain,(
% 19.29/2.98    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f45])).
% 19.29/2.98  
% 19.29/2.98  fof(f105,plain,(
% 19.29/2.98    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f45])).
% 19.29/2.98  
% 19.29/2.98  fof(f106,plain,(
% 19.29/2.98    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f45])).
% 19.29/2.98  
% 19.29/2.98  fof(f125,plain,(
% 19.29/2.98    ~v2_struct_0(sK3)),
% 19.29/2.98    inference(cnf_transformation,[],[f77])).
% 19.29/2.98  
% 19.29/2.98  fof(f126,plain,(
% 19.29/2.98    v2_pre_topc(sK3)),
% 19.29/2.98    inference(cnf_transformation,[],[f77])).
% 19.29/2.98  
% 19.29/2.98  fof(f127,plain,(
% 19.29/2.98    l1_pre_topc(sK3)),
% 19.29/2.98    inference(cnf_transformation,[],[f77])).
% 19.29/2.98  
% 19.29/2.98  fof(f12,axiom,(
% 19.29/2.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f42,plain,(
% 19.29/2.98    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f12])).
% 19.29/2.98  
% 19.29/2.98  fof(f43,plain,(
% 19.29/2.98    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f42])).
% 19.29/2.98  
% 19.29/2.98  fof(f103,plain,(
% 19.29/2.98    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f43])).
% 19.29/2.98  
% 19.29/2.98  fof(f8,axiom,(
% 19.29/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f35,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f8])).
% 19.29/2.98  
% 19.29/2.98  fof(f36,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f35])).
% 19.29/2.98  
% 19.29/2.98  fof(f69,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(nnf_transformation,[],[f36])).
% 19.29/2.98  
% 19.29/2.98  fof(f70,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(rectify,[],[f69])).
% 19.29/2.98  
% 19.29/2.98  fof(f71,plain,(
% 19.29/2.98    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.29/2.98    introduced(choice_axiom,[])).
% 19.29/2.98  
% 19.29/2.98  fof(f72,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f70,f71])).
% 19.29/2.98  
% 19.29/2.98  fof(f91,plain,(
% 19.29/2.98    ( ! [X2,X0,X1] : (k9_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f72])).
% 19.29/2.98  
% 19.29/2.98  fof(f102,plain,(
% 19.29/2.98    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f43])).
% 19.29/2.98  
% 19.29/2.98  fof(f6,axiom,(
% 19.29/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f31,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f6])).
% 19.29/2.98  
% 19.29/2.98  fof(f32,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f31])).
% 19.29/2.98  
% 19.29/2.98  fof(f84,plain,(
% 19.29/2.98    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f32])).
% 19.29/2.98  
% 19.29/2.98  fof(f131,plain,(
% 19.29/2.98    m1_pre_topc(sK5,sK3)),
% 19.29/2.98    inference(cnf_transformation,[],[f77])).
% 19.29/2.98  
% 19.29/2.98  fof(f4,axiom,(
% 19.29/2.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f27,plain,(
% 19.29/2.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f4])).
% 19.29/2.98  
% 19.29/2.98  fof(f28,plain,(
% 19.29/2.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f27])).
% 19.29/2.98  
% 19.29/2.98  fof(f81,plain,(
% 19.29/2.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f28])).
% 19.29/2.98  
% 19.29/2.98  fof(f1,axiom,(
% 19.29/2.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f24,plain,(
% 19.29/2.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 19.29/2.98    inference(ennf_transformation,[],[f1])).
% 19.29/2.98  
% 19.29/2.98  fof(f78,plain,(
% 19.29/2.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f24])).
% 19.29/2.98  
% 19.29/2.98  fof(f14,axiom,(
% 19.29/2.98    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f46,plain,(
% 19.29/2.98    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f14])).
% 19.29/2.98  
% 19.29/2.98  fof(f47,plain,(
% 19.29/2.98    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f46])).
% 19.29/2.98  
% 19.29/2.98  fof(f107,plain,(
% 19.29/2.98    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f47])).
% 19.29/2.98  
% 19.29/2.98  fof(f101,plain,(
% 19.29/2.98    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f43])).
% 19.29/2.98  
% 19.29/2.98  fof(f21,axiom,(
% 19.29/2.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f59,plain,(
% 19.29/2.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 19.29/2.98    inference(ennf_transformation,[],[f21])).
% 19.29/2.98  
% 19.29/2.98  fof(f124,plain,(
% 19.29/2.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f59])).
% 19.29/2.98  
% 19.29/2.98  fof(f18,axiom,(
% 19.29/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f54,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f18])).
% 19.29/2.98  
% 19.29/2.98  fof(f55,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f54])).
% 19.29/2.98  
% 19.29/2.98  fof(f117,plain,(
% 19.29/2.98    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f55])).
% 19.29/2.98  
% 19.29/2.98  fof(f109,plain,(
% 19.29/2.98    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f47])).
% 19.29/2.98  
% 19.29/2.98  fof(f108,plain,(
% 19.29/2.98    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f47])).
% 19.29/2.98  
% 19.29/2.98  fof(f89,plain,(
% 19.29/2.98    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f72])).
% 19.29/2.98  
% 19.29/2.98  fof(f137,plain,(
% 19.29/2.98    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(equality_resolution,[],[f89])).
% 19.29/2.98  
% 19.29/2.98  fof(f138,plain,(
% 19.29/2.98    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(equality_resolution,[],[f137])).
% 19.29/2.98  
% 19.29/2.98  fof(f5,axiom,(
% 19.29/2.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f29,plain,(
% 19.29/2.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 19.29/2.98    inference(ennf_transformation,[],[f5])).
% 19.29/2.98  
% 19.29/2.98  fof(f30,plain,(
% 19.29/2.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 19.29/2.98    inference(flattening,[],[f29])).
% 19.29/2.98  
% 19.29/2.98  fof(f64,plain,(
% 19.29/2.98    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 19.29/2.98    inference(nnf_transformation,[],[f30])).
% 19.29/2.98  
% 19.29/2.98  fof(f82,plain,(
% 19.29/2.98    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f64])).
% 19.29/2.98  
% 19.29/2.98  fof(f19,axiom,(
% 19.29/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f56,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : (((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f19])).
% 19.29/2.98  
% 19.29/2.98  fof(f57,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (! [X2] : ((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f56])).
% 19.29/2.98  
% 19.29/2.98  fof(f121,plain,(
% 19.29/2.98    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f57])).
% 19.29/2.98  
% 19.29/2.98  fof(f133,plain,(
% 19.29/2.98    ~m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))),
% 19.29/2.98    inference(cnf_transformation,[],[f77])).
% 19.29/2.98  
% 19.29/2.98  fof(f130,plain,(
% 19.29/2.98    ~v2_struct_0(sK5)),
% 19.29/2.98    inference(cnf_transformation,[],[f77])).
% 19.29/2.98  
% 19.29/2.98  fof(f2,axiom,(
% 19.29/2.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f25,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.29/2.98    inference(ennf_transformation,[],[f2])).
% 19.29/2.98  
% 19.29/2.98  fof(f79,plain,(
% 19.29/2.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f25])).
% 19.29/2.98  
% 19.29/2.98  fof(f10,axiom,(
% 19.29/2.98    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f38,plain,(
% 19.29/2.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f10])).
% 19.29/2.98  
% 19.29/2.98  fof(f39,plain,(
% 19.29/2.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f38])).
% 19.29/2.98  
% 19.29/2.98  fof(f95,plain,(
% 19.29/2.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f39])).
% 19.29/2.98  
% 19.29/2.98  fof(f96,plain,(
% 19.29/2.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f39])).
% 19.29/2.98  
% 19.29/2.98  fof(f132,plain,(
% 19.29/2.98    r1_tsep_1(sK4,sK5)),
% 19.29/2.98    inference(cnf_transformation,[],[f77])).
% 19.29/2.98  
% 19.29/2.98  fof(f17,axiom,(
% 19.29/2.98    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f52,plain,(
% 19.29/2.98    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 19.29/2.98    inference(ennf_transformation,[],[f17])).
% 19.29/2.98  
% 19.29/2.98  fof(f53,plain,(
% 19.29/2.98    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 19.29/2.98    inference(flattening,[],[f52])).
% 19.29/2.98  
% 19.29/2.98  fof(f116,plain,(
% 19.29/2.98    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f53])).
% 19.29/2.98  
% 19.29/2.98  fof(f97,plain,(
% 19.29/2.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f39])).
% 19.29/2.98  
% 19.29/2.98  fof(f9,axiom,(
% 19.29/2.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 19.29/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.29/2.98  
% 19.29/2.98  fof(f37,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 19.29/2.98    inference(ennf_transformation,[],[f9])).
% 19.29/2.98  
% 19.29/2.98  fof(f73,plain,(
% 19.29/2.98    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 19.29/2.98    inference(nnf_transformation,[],[f37])).
% 19.29/2.98  
% 19.29/2.98  fof(f93,plain,(
% 19.29/2.98    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.29/2.98    inference(cnf_transformation,[],[f73])).
% 19.29/2.98  
% 19.29/2.98  cnf(c_51,negated_conjecture,
% 19.29/2.98      ( m1_pre_topc(sK4,sK3) ),
% 19.29/2.98      inference(cnf_transformation,[],[f129]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_6071,negated_conjecture,
% 19.29/2.98      ( m1_pre_topc(sK4,sK3) ),
% 19.29/2.98      inference(subtyping,[status(esa)],[c_51]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_7127,plain,
% 19.29/2.98      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 19.29/2.98      inference(predicate_to_equality,[status(thm)],[c_6071]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_10,plain,
% 19.29/2.98      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.29/2.98      | ~ m1_pre_topc(X0,X1)
% 19.29/2.98      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 19.29/2.98      | ~ v2_pre_topc(X1)
% 19.29/2.98      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 19.29/2.98      | v2_struct_0(X1)
% 19.29/2.98      | ~ l1_pre_topc(X1)
% 19.29/2.98      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 19.29/2.98      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 19.29/2.98      inference(cnf_transformation,[],[f136]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_45,plain,
% 19.29/2.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.29/2.98      | ~ m1_pre_topc(X0,X1)
% 19.29/2.98      | ~ l1_pre_topc(X1) ),
% 19.29/2.98      inference(cnf_transformation,[],[f123]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_28,plain,
% 19.29/2.98      ( ~ m1_pre_topc(X0,X1)
% 19.29/2.98      | v1_pre_topc(k8_tmap_1(X1,X0))
% 19.29/2.98      | ~ v2_pre_topc(X1)
% 19.29/2.98      | v2_struct_0(X1)
% 19.29/2.98      | ~ l1_pre_topc(X1) ),
% 19.29/2.98      inference(cnf_transformation,[],[f104]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_27,plain,
% 19.29/2.98      ( ~ m1_pre_topc(X0,X1)
% 19.29/2.98      | ~ v2_pre_topc(X1)
% 19.29/2.98      | v2_pre_topc(k8_tmap_1(X1,X0))
% 19.29/2.98      | v2_struct_0(X1)
% 19.29/2.98      | ~ l1_pre_topc(X1) ),
% 19.29/2.98      inference(cnf_transformation,[],[f105]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_26,plain,
% 19.29/2.98      ( ~ m1_pre_topc(X0,X1)
% 19.29/2.98      | ~ v2_pre_topc(X1)
% 19.29/2.98      | v2_struct_0(X1)
% 19.29/2.98      | ~ l1_pre_topc(X1)
% 19.29/2.98      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 19.29/2.98      inference(cnf_transformation,[],[f106]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_362,plain,
% 19.29/2.98      ( ~ l1_pre_topc(X1)
% 19.29/2.98      | v2_struct_0(X1)
% 19.29/2.98      | ~ m1_pre_topc(X0,X1)
% 19.29/2.98      | ~ v2_pre_topc(X1)
% 19.29/2.98      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 19.29/2.98      inference(global_propositional_subsumption,
% 19.29/2.98                [status(thm)],
% 19.29/2.98                [c_10,c_45,c_28,c_27,c_26]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_363,plain,
% 19.29/2.98      ( ~ m1_pre_topc(X0,X1)
% 19.29/2.98      | ~ v2_pre_topc(X1)
% 19.29/2.98      | v2_struct_0(X1)
% 19.29/2.98      | ~ l1_pre_topc(X1)
% 19.29/2.98      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 19.29/2.98      inference(renaming,[status(thm)],[c_362]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_6065,plain,
% 19.29/2.98      ( ~ m1_pre_topc(X0_61,X1_61)
% 19.29/2.98      | ~ v2_pre_topc(X1_61)
% 19.29/2.98      | v2_struct_0(X1_61)
% 19.29/2.98      | ~ l1_pre_topc(X1_61)
% 19.29/2.98      | k6_tmap_1(X1_61,u1_struct_0(X0_61)) = k8_tmap_1(X1_61,X0_61) ),
% 19.29/2.98      inference(subtyping,[status(esa)],[c_363]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_7133,plain,
% 19.29/2.98      ( k6_tmap_1(X0_61,u1_struct_0(X1_61)) = k8_tmap_1(X0_61,X1_61)
% 19.29/2.98      | m1_pre_topc(X1_61,X0_61) != iProver_top
% 19.29/2.98      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.98      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.98      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.98      inference(predicate_to_equality,[status(thm)],[c_6065]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_9306,plain,
% 19.29/2.98      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
% 19.29/2.98      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.98      | v2_struct_0(sK3) = iProver_top
% 19.29/2.98      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.98      inference(superposition,[status(thm)],[c_7127,c_7133]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_55,negated_conjecture,
% 19.29/2.98      ( ~ v2_struct_0(sK3) ),
% 19.29/2.98      inference(cnf_transformation,[],[f125]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_56,plain,
% 19.29/2.98      ( v2_struct_0(sK3) != iProver_top ),
% 19.29/2.98      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_54,negated_conjecture,
% 19.29/2.98      ( v2_pre_topc(sK3) ),
% 19.29/2.98      inference(cnf_transformation,[],[f126]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_57,plain,
% 19.29/2.98      ( v2_pre_topc(sK3) = iProver_top ),
% 19.29/2.98      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_53,negated_conjecture,
% 19.29/2.98      ( l1_pre_topc(sK3) ),
% 19.29/2.98      inference(cnf_transformation,[],[f127]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_58,plain,
% 19.29/2.98      ( l1_pre_topc(sK3) = iProver_top ),
% 19.29/2.98      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_9421,plain,
% 19.29/2.98      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 19.29/2.98      inference(global_propositional_subsumption,
% 19.29/2.98                [status(thm)],
% 19.29/2.98                [c_9306,c_56,c_57,c_58]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_23,plain,
% 19.29/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.29/2.98      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 19.29/2.98      | ~ v2_pre_topc(X1)
% 19.29/2.98      | v2_struct_0(X1)
% 19.29/2.98      | ~ l1_pre_topc(X1) ),
% 19.29/2.98      inference(cnf_transformation,[],[f103]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_6094,plain,
% 19.29/2.98      ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
% 19.29/2.98      | m1_subset_1(k7_tmap_1(X0_61,X0_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,X0_60)))))
% 19.29/2.98      | ~ v2_pre_topc(X0_61)
% 19.29/2.98      | v2_struct_0(X0_61)
% 19.29/2.98      | ~ l1_pre_topc(X0_61) ),
% 19.29/2.98      inference(subtyping,[status(esa)],[c_23]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_7104,plain,
% 19.29/2.98      ( m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
% 19.29/2.98      | m1_subset_1(k7_tmap_1(X0_61,X0_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,X0_60))))) = iProver_top
% 19.29/2.98      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.98      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.98      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.98      inference(predicate_to_equality,[status(thm)],[c_6094]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_10291,plain,
% 19.29/2.98      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
% 19.29/2.98      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.29/2.98      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.98      | v2_struct_0(sK3) = iProver_top
% 19.29/2.98      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.98      inference(superposition,[status(thm)],[c_9421,c_7104]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_2267,plain,
% 19.29/2.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.29/2.98      | ~ l1_pre_topc(X1)
% 19.29/2.98      | sK4 != X0
% 19.29/2.98      | sK3 != X1 ),
% 19.29/2.98      inference(resolution_lifted,[status(thm)],[c_45,c_51]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_2268,plain,
% 19.29/2.98      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.29/2.98      | ~ l1_pre_topc(sK3) ),
% 19.29/2.98      inference(unflattening,[status(thm)],[c_2267]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_2269,plain,
% 19.29/2.98      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 19.29/2.98      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.98      inference(predicate_to_equality,[status(thm)],[c_2268]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_10926,plain,
% 19.29/2.98      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
% 19.29/2.98      inference(global_propositional_subsumption,
% 19.29/2.98                [status(thm)],
% 19.29/2.98                [c_10291,c_56,c_57,c_58,c_2269]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_12,plain,
% 19.29/2.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
% 19.29/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
% 19.29/2.98      | ~ m1_pre_topc(X2,X1)
% 19.29/2.98      | ~ v2_pre_topc(X1)
% 19.29/2.98      | ~ v1_funct_1(X0)
% 19.29/2.98      | v2_struct_0(X1)
% 19.29/2.98      | ~ l1_pre_topc(X1)
% 19.29/2.98      | sK2(X1,X2,X0) = u1_struct_0(X2)
% 19.29/2.98      | k9_tmap_1(X1,X2) = X0 ),
% 19.29/2.98      inference(cnf_transformation,[],[f91]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_6104,plain,
% 19.29/2.98      ( ~ v1_funct_2(X0_60,u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)))
% 19.29/2.98      | ~ m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)))))
% 19.29/2.98      | ~ m1_pre_topc(X1_61,X0_61)
% 19.29/2.98      | ~ v2_pre_topc(X0_61)
% 19.29/2.98      | ~ v1_funct_1(X0_60)
% 19.29/2.98      | v2_struct_0(X0_61)
% 19.29/2.98      | ~ l1_pre_topc(X0_61)
% 19.29/2.98      | sK2(X0_61,X1_61,X0_60) = u1_struct_0(X1_61)
% 19.29/2.98      | k9_tmap_1(X0_61,X1_61) = X0_60 ),
% 19.29/2.98      inference(subtyping,[status(esa)],[c_12]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_7094,plain,
% 19.29/2.98      ( sK2(X0_61,X1_61,X0_60) = u1_struct_0(X1_61)
% 19.29/2.98      | k9_tmap_1(X0_61,X1_61) = X0_60
% 19.29/2.98      | v1_funct_2(X0_60,u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61))) != iProver_top
% 19.29/2.98      | m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61))))) != iProver_top
% 19.29/2.98      | m1_pre_topc(X1_61,X0_61) != iProver_top
% 19.29/2.98      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.98      | v1_funct_1(X0_60) != iProver_top
% 19.29/2.98      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.98      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.98      inference(predicate_to_equality,[status(thm)],[c_6104]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_11100,plain,
% 19.29/2.98      ( sK2(sK3,sK4,k7_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK4)
% 19.29/2.98      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 19.29/2.98      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 19.29/2.98      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.29/2.98      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.98      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 19.29/2.98      | v2_struct_0(sK3) = iProver_top
% 19.29/2.98      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.98      inference(superposition,[status(thm)],[c_10926,c_7094]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_60,plain,
% 19.29/2.98      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 19.29/2.98      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_24,plain,
% 19.29/2.98      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 19.29/2.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.29/2.98      | ~ v2_pre_topc(X0)
% 19.29/2.98      | v2_struct_0(X0)
% 19.29/2.98      | ~ l1_pre_topc(X0) ),
% 19.29/2.98      inference(cnf_transformation,[],[f102]) ).
% 19.29/2.98  
% 19.29/2.98  cnf(c_6093,plain,
% 19.29/2.98      ( v1_funct_2(k7_tmap_1(X0_61,X0_60),u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,X0_60)))
% 19.29/2.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
% 19.29/2.99      | ~ v2_pre_topc(X0_61)
% 19.29/2.99      | v2_struct_0(X0_61)
% 19.29/2.99      | ~ l1_pre_topc(X0_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_24]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7105,plain,
% 19.29/2.99      ( v1_funct_2(k7_tmap_1(X0_61,X0_60),u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,X0_60))) = iProver_top
% 19.29/2.99      | m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6093]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_9759,plain,
% 19.29/2.99      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
% 19.29/2.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_9421,c_7105]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_45674,plain,
% 19.29/2.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 19.29/2.99      | sK2(sK3,sK4,k7_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK4)
% 19.29/2.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_11100,c_56,c_57,c_58,c_60,c_2269,c_9759]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_45675,plain,
% 19.29/2.99      ( sK2(sK3,sK4,k7_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK4)
% 19.29/2.99      | k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 19.29/2.99      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
% 19.29/2.99      inference(renaming,[status(thm)],[c_45674]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6076,plain,
% 19.29/2.99      ( m1_subset_1(u1_struct_0(X0_61),k1_zfmisc_1(u1_struct_0(X1_61)))
% 19.29/2.99      | ~ m1_pre_topc(X0_61,X1_61)
% 19.29/2.99      | ~ l1_pre_topc(X1_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_45]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7122,plain,
% 19.29/2.99      ( m1_subset_1(u1_struct_0(X0_61),k1_zfmisc_1(u1_struct_0(X1_61))) = iProver_top
% 19.29/2.99      | m1_pre_topc(X0_61,X1_61) != iProver_top
% 19.29/2.99      | l1_pre_topc(X1_61) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6076]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6,plain,
% 19.29/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.29/2.99      | ~ v2_pre_topc(X1)
% 19.29/2.99      | v2_struct_0(X1)
% 19.29/2.99      | ~ l1_pre_topc(X1)
% 19.29/2.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 19.29/2.99      inference(cnf_transformation,[],[f84]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6109,plain,
% 19.29/2.99      ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
% 19.29/2.99      | ~ v2_pre_topc(X0_61)
% 19.29/2.99      | v2_struct_0(X0_61)
% 19.29/2.99      | ~ l1_pre_topc(X0_61)
% 19.29/2.99      | k7_tmap_1(X0_61,X0_60) = k6_partfun1(u1_struct_0(X0_61)) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_6]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7089,plain,
% 19.29/2.99      ( k7_tmap_1(X0_61,X0_60) = k6_partfun1(u1_struct_0(X0_61))
% 19.29/2.99      | m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6109]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_8844,plain,
% 19.29/2.99      ( k7_tmap_1(X0_61,u1_struct_0(X1_61)) = k6_partfun1(u1_struct_0(X0_61))
% 19.29/2.99      | m1_pre_topc(X1_61,X0_61) != iProver_top
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7122,c_7089]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11604,plain,
% 19.29/2.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3))
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7127,c_8844]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11784,plain,
% 19.29/2.99      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_11604,c_56,c_57,c_58]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_45678,plain,
% 19.29/2.99      ( sK2(sK3,sK4,k6_partfun1(u1_struct_0(sK3))) = u1_struct_0(sK4)
% 19.29/2.99      | k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 19.29/2.99      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
% 19.29/2.99      inference(light_normalisation,[status(thm)],[c_45675,c_11784]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_49,negated_conjecture,
% 19.29/2.99      ( m1_pre_topc(sK5,sK3) ),
% 19.29/2.99      inference(cnf_transformation,[],[f131]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_62,plain,
% 19.29/2.99      ( m1_pre_topc(sK5,sK3) = iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_3,plain,
% 19.29/2.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 19.29/2.99      inference(cnf_transformation,[],[f81]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_188,plain,
% 19.29/2.99      ( v2_struct_0(X0) = iProver_top
% 19.29/2.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 19.29/2.99      | l1_struct_0(X0) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_190,plain,
% 19.29/2.99      ( v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 19.29/2.99      | l1_struct_0(sK3) != iProver_top ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_188]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_0,plain,
% 19.29/2.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 19.29/2.99      inference(cnf_transformation,[],[f78]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_195,plain,
% 19.29/2.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_197,plain,
% 19.29/2.99      ( l1_pre_topc(sK3) != iProver_top | l1_struct_0(sK3) = iProver_top ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_195]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_31,plain,
% 19.29/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.29/2.99      | ~ v2_pre_topc(X1)
% 19.29/2.99      | v1_funct_1(k9_tmap_1(X1,X0))
% 19.29/2.99      | v2_struct_0(X1)
% 19.29/2.99      | ~ l1_pre_topc(X1) ),
% 19.29/2.99      inference(cnf_transformation,[],[f107]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_2280,plain,
% 19.29/2.99      ( ~ v2_pre_topc(X0)
% 19.29/2.99      | v1_funct_1(k9_tmap_1(X0,X1))
% 19.29/2.99      | v2_struct_0(X0)
% 19.29/2.99      | ~ l1_pre_topc(X0)
% 19.29/2.99      | sK4 != X1
% 19.29/2.99      | sK3 != X0 ),
% 19.29/2.99      inference(resolution_lifted,[status(thm)],[c_31,c_51]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_2281,plain,
% 19.29/2.99      ( ~ v2_pre_topc(sK3)
% 19.29/2.99      | v1_funct_1(k9_tmap_1(sK3,sK4))
% 19.29/2.99      | v2_struct_0(sK3)
% 19.29/2.99      | ~ l1_pre_topc(sK3) ),
% 19.29/2.99      inference(unflattening,[status(thm)],[c_2280]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_2282,plain,
% 19.29/2.99      ( v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v1_funct_1(k9_tmap_1(sK3,sK4)) = iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_2281]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6073,negated_conjecture,
% 19.29/2.99      ( m1_pre_topc(sK5,sK3) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_49]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7125,plain,
% 19.29/2.99      ( m1_pre_topc(sK5,sK3) = iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6073]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11603,plain,
% 19.29/2.99      ( k7_tmap_1(sK3,u1_struct_0(sK5)) = k6_partfun1(u1_struct_0(sK3))
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7125,c_8844]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11745,plain,
% 19.29/2.99      ( k7_tmap_1(sK3,u1_struct_0(sK5)) = k6_partfun1(u1_struct_0(sK3)) ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_11603,c_56,c_57,c_58]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_25,plain,
% 19.29/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.29/2.99      | ~ v2_pre_topc(X1)
% 19.29/2.99      | v1_funct_1(k7_tmap_1(X1,X0))
% 19.29/2.99      | v2_struct_0(X1)
% 19.29/2.99      | ~ l1_pre_topc(X1) ),
% 19.29/2.99      inference(cnf_transformation,[],[f101]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6092,plain,
% 19.29/2.99      ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
% 19.29/2.99      | ~ v2_pre_topc(X0_61)
% 19.29/2.99      | v1_funct_1(k7_tmap_1(X0_61,X0_60))
% 19.29/2.99      | v2_struct_0(X0_61)
% 19.29/2.99      | ~ l1_pre_topc(X0_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_25]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7106,plain,
% 19.29/2.99      ( m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v1_funct_1(k7_tmap_1(X0_61,X0_60)) = iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6092]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_8917,plain,
% 19.29/2.99      ( m1_pre_topc(X0_61,X1_61) != iProver_top
% 19.29/2.99      | v2_pre_topc(X1_61) != iProver_top
% 19.29/2.99      | v1_funct_1(k7_tmap_1(X1_61,u1_struct_0(X0_61))) = iProver_top
% 19.29/2.99      | v2_struct_0(X1_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X1_61) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7122,c_7106]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11764,plain,
% 19.29/2.99      ( m1_pre_topc(sK5,sK3) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) = iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_11745,c_8917]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6068,negated_conjecture,
% 19.29/2.99      ( v2_pre_topc(sK3) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_54]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7130,plain,
% 19.29/2.99      ( v2_pre_topc(sK3) = iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6068]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_46,plain,
% 19.29/2.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 19.29/2.99      inference(cnf_transformation,[],[f124]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6075,plain,
% 19.29/2.99      ( m1_pre_topc(X0_61,X0_61) | ~ l1_pre_topc(X0_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_46]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7123,plain,
% 19.29/2.99      ( m1_pre_topc(X0_61,X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6075]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_40,plain,
% 19.29/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.29/2.99      | ~ v2_pre_topc(X1)
% 19.29/2.99      | v2_struct_0(X1)
% 19.29/2.99      | ~ l1_pre_topc(X1)
% 19.29/2.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 19.29/2.99      inference(cnf_transformation,[],[f117]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6080,plain,
% 19.29/2.99      ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
% 19.29/2.99      | ~ v2_pre_topc(X0_61)
% 19.29/2.99      | v2_struct_0(X0_61)
% 19.29/2.99      | ~ l1_pre_topc(X0_61)
% 19.29/2.99      | u1_struct_0(k6_tmap_1(X0_61,X0_60)) = u1_struct_0(X0_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_40]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7118,plain,
% 19.29/2.99      ( u1_struct_0(k6_tmap_1(X0_61,X0_60)) = u1_struct_0(X0_61)
% 19.29/2.99      | m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6080]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_9024,plain,
% 19.29/2.99      ( u1_struct_0(k6_tmap_1(X0_61,u1_struct_0(X1_61))) = u1_struct_0(X0_61)
% 19.29/2.99      | m1_pre_topc(X1_61,X0_61) != iProver_top
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7122,c_7118]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_12631,plain,
% 19.29/2.99      ( u1_struct_0(k6_tmap_1(X0_61,u1_struct_0(X0_61))) = u1_struct_0(X0_61)
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7123,c_9024]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_12722,plain,
% 19.29/2.99      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3)
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7130,c_12631]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_9307,plain,
% 19.29/2.99      ( k6_tmap_1(X0_61,u1_struct_0(X0_61)) = k8_tmap_1(X0_61,X0_61)
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7123,c_7133]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_10062,plain,
% 19.29/2.99      ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3)
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7130,c_9307]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_66,plain,
% 19.29/2.99      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_46]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6274,plain,
% 19.29/2.99      ( ~ m1_pre_topc(sK3,sK3)
% 19.29/2.99      | ~ v2_pre_topc(sK3)
% 19.29/2.99      | v2_struct_0(sK3)
% 19.29/2.99      | ~ l1_pre_topc(sK3)
% 19.29/2.99      | k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_6065]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_10180,plain,
% 19.29/2.99      ( k6_tmap_1(sK3,u1_struct_0(sK3)) = k8_tmap_1(sK3,sK3) ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_10062,c_55,c_54,c_53,c_66,c_6274]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_12725,plain,
% 19.29/2.99      ( u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3)
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(light_normalisation,[status(thm)],[c_12722,c_10180]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_13149,plain,
% 19.29/2.99      ( u1_struct_0(k8_tmap_1(sK3,sK3)) = u1_struct_0(sK3) ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_12725,c_56,c_58]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11605,plain,
% 19.29/2.99      ( k7_tmap_1(X0_61,u1_struct_0(X0_61)) = k6_partfun1(u1_struct_0(X0_61))
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7123,c_8844]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11914,plain,
% 19.29/2.99      ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3))
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7130,c_11605]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_69,plain,
% 19.29/2.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.29/2.99      | ~ m1_pre_topc(sK3,sK3)
% 19.29/2.99      | ~ l1_pre_topc(sK3) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_45]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7227,plain,
% 19.29/2.99      ( ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(sK3)))
% 19.29/2.99      | ~ v2_pre_topc(sK3)
% 19.29/2.99      | v2_struct_0(sK3)
% 19.29/2.99      | ~ l1_pre_topc(sK3)
% 19.29/2.99      | k7_tmap_1(sK3,X0_60) = k6_partfun1(u1_struct_0(sK3)) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_6109]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7590,plain,
% 19.29/2.99      ( ~ m1_subset_1(u1_struct_0(X0_61),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.29/2.99      | ~ v2_pre_topc(sK3)
% 19.29/2.99      | v2_struct_0(sK3)
% 19.29/2.99      | ~ l1_pre_topc(sK3)
% 19.29/2.99      | k7_tmap_1(sK3,u1_struct_0(X0_61)) = k6_partfun1(u1_struct_0(sK3)) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_7227]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7592,plain,
% 19.29/2.99      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.29/2.99      | ~ v2_pre_topc(sK3)
% 19.29/2.99      | v2_struct_0(sK3)
% 19.29/2.99      | ~ l1_pre_topc(sK3)
% 19.29/2.99      | k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_7590]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11925,plain,
% 19.29/2.99      ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_11914,c_55,c_54,c_53,c_66,c_69,c_7592]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_10289,plain,
% 19.29/2.99      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) = iProver_top
% 19.29/2.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_10180,c_7104]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_65,plain,
% 19.29/2.99      ( m1_pre_topc(X0,X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_67,plain,
% 19.29/2.99      ( m1_pre_topc(sK3,sK3) = iProver_top | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_65]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_68,plain,
% 19.29/2.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 19.29/2.99      | m1_pre_topc(X0,X1) != iProver_top
% 19.29/2.99      | l1_pre_topc(X1) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_70,plain,
% 19.29/2.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 19.29/2.99      | m1_pre_topc(sK3,sK3) != iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_68]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_10841,plain,
% 19.29/2.99      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) = iProver_top ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_10289,c_56,c_57,c_58,c_67,c_70]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11928,plain,
% 19.29/2.99      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))))) = iProver_top ),
% 19.29/2.99      inference(demodulation,[status(thm)],[c_11925,c_10841]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_13151,plain,
% 19.29/2.99      ( m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
% 19.29/2.99      inference(demodulation,[status(thm)],[c_13149,c_11928]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_10182,plain,
% 19.29/2.99      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top
% 19.29/2.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_10180,c_7105]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_10836,plain,
% 19.29/2.99      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_10182,c_56,c_57,c_58,c_67,c_70]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11929,plain,
% 19.29/2.99      ( v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK3))) = iProver_top ),
% 19.29/2.99      inference(demodulation,[status(thm)],[c_11925,c_10836]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_13152,plain,
% 19.29/2.99      ( v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 19.29/2.99      inference(demodulation,[status(thm)],[c_13149,c_11929]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_12630,plain,
% 19.29/2.99      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3)
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7127,c_9024]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_12633,plain,
% 19.29/2.99      ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3)
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(light_normalisation,[status(thm)],[c_12630,c_9421]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_13351,plain,
% 19.29/2.99      ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3) ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_12633,c_56,c_57,c_58]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_29,plain,
% 19.29/2.99      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 19.29/2.99      | ~ m1_pre_topc(X1,X0)
% 19.29/2.99      | ~ v2_pre_topc(X0)
% 19.29/2.99      | v2_struct_0(X0)
% 19.29/2.99      | ~ l1_pre_topc(X0) ),
% 19.29/2.99      inference(cnf_transformation,[],[f109]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6088,plain,
% 19.29/2.99      ( m1_subset_1(k9_tmap_1(X0_61,X1_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)))))
% 19.29/2.99      | ~ m1_pre_topc(X1_61,X0_61)
% 19.29/2.99      | ~ v2_pre_topc(X0_61)
% 19.29/2.99      | v2_struct_0(X0_61)
% 19.29/2.99      | ~ l1_pre_topc(X0_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_29]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7110,plain,
% 19.29/2.99      ( m1_subset_1(k9_tmap_1(X0_61,X1_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61))))) = iProver_top
% 19.29/2.99      | m1_pre_topc(X1_61,X0_61) != iProver_top
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6088]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_13403,plain,
% 19.29/2.99      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top
% 19.29/2.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_13351,c_7110]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_30,plain,
% 19.29/2.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 19.29/2.99      | ~ m1_pre_topc(X1,X0)
% 19.29/2.99      | ~ v2_pre_topc(X0)
% 19.29/2.99      | v2_struct_0(X0)
% 19.29/2.99      | ~ l1_pre_topc(X0) ),
% 19.29/2.99      inference(cnf_transformation,[],[f108]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6087,plain,
% 19.29/2.99      ( v1_funct_2(k9_tmap_1(X0_61,X1_61),u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)))
% 19.29/2.99      | ~ m1_pre_topc(X1_61,X0_61)
% 19.29/2.99      | ~ v2_pre_topc(X0_61)
% 19.29/2.99      | v2_struct_0(X0_61)
% 19.29/2.99      | ~ l1_pre_topc(X0_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_30]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7111,plain,
% 19.29/2.99      ( v1_funct_2(k9_tmap_1(X0_61,X1_61),u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61))) = iProver_top
% 19.29/2.99      | m1_pre_topc(X1_61,X0_61) != iProver_top
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6087]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_13404,plain,
% 19.29/2.99      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top
% 19.29/2.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_13351,c_7111]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_14,plain,
% 19.29/2.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 19.29/2.99      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 19.29/2.99      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 19.29/2.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 19.29/2.99      | ~ m1_pre_topc(X1,X0)
% 19.29/2.99      | ~ v2_pre_topc(X0)
% 19.29/2.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 19.29/2.99      | v2_struct_0(X0)
% 19.29/2.99      | ~ l1_pre_topc(X0) ),
% 19.29/2.99      inference(cnf_transformation,[],[f138]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_352,plain,
% 19.29/2.99      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 19.29/2.99      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 19.29/2.99      | ~ m1_pre_topc(X1,X0)
% 19.29/2.99      | ~ v2_pre_topc(X0)
% 19.29/2.99      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 19.29/2.99      | v2_struct_0(X0)
% 19.29/2.99      | ~ l1_pre_topc(X0) ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_14,c_30,c_29]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6066,plain,
% 19.29/2.99      ( r1_funct_2(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)),u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,u1_struct_0(X1_61))),k9_tmap_1(X0_61,X1_61),k7_tmap_1(X0_61,u1_struct_0(X1_61)))
% 19.29/2.99      | ~ m1_subset_1(u1_struct_0(X1_61),k1_zfmisc_1(u1_struct_0(X0_61)))
% 19.29/2.99      | ~ m1_pre_topc(X1_61,X0_61)
% 19.29/2.99      | ~ v2_pre_topc(X0_61)
% 19.29/2.99      | ~ v1_funct_1(k9_tmap_1(X0_61,X1_61))
% 19.29/2.99      | v2_struct_0(X0_61)
% 19.29/2.99      | ~ l1_pre_topc(X0_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_352]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7132,plain,
% 19.29/2.99      ( r1_funct_2(u1_struct_0(X0_61),u1_struct_0(k8_tmap_1(X0_61,X1_61)),u1_struct_0(X0_61),u1_struct_0(k6_tmap_1(X0_61,u1_struct_0(X1_61))),k9_tmap_1(X0_61,X1_61),k7_tmap_1(X0_61,u1_struct_0(X1_61))) = iProver_top
% 19.29/2.99      | m1_subset_1(u1_struct_0(X1_61),k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
% 19.29/2.99      | m1_pre_topc(X1_61,X0_61) != iProver_top
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v1_funct_1(k9_tmap_1(X0_61,X1_61)) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6066]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_13399,plain,
% 19.29/2.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
% 19.29/2.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.29/2.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_13351,c_7132]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_13410,plain,
% 19.29/2.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),k9_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3))) = iProver_top
% 19.29/2.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.29/2.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.29/2.99      inference(light_normalisation,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_13399,c_9421,c_11784,c_13351]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_14836,plain,
% 19.29/2.99      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),k9_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3))) = iProver_top ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_13410,c_56,c_57,c_58,c_60,c_2269,c_2282]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_5,plain,
% 19.29/2.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 19.29/2.99      | ~ v1_funct_2(X5,X2,X3)
% 19.29/2.99      | ~ v1_funct_2(X4,X0,X1)
% 19.29/2.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 19.29/2.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.29/2.99      | ~ v1_funct_1(X5)
% 19.29/2.99      | ~ v1_funct_1(X4)
% 19.29/2.99      | v1_xboole_0(X1)
% 19.29/2.99      | v1_xboole_0(X3)
% 19.29/2.99      | X4 = X5 ),
% 19.29/2.99      inference(cnf_transformation,[],[f82]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6110,plain,
% 19.29/2.99      ( ~ r1_funct_2(X0_60,X1_60,X2_60,X3_60,X4_60,X5_60)
% 19.29/2.99      | ~ v1_funct_2(X5_60,X2_60,X3_60)
% 19.29/2.99      | ~ v1_funct_2(X4_60,X0_60,X1_60)
% 19.29/2.99      | ~ m1_subset_1(X5_60,k1_zfmisc_1(k2_zfmisc_1(X2_60,X3_60)))
% 19.29/2.99      | ~ m1_subset_1(X4_60,k1_zfmisc_1(k2_zfmisc_1(X0_60,X1_60)))
% 19.29/2.99      | ~ v1_funct_1(X5_60)
% 19.29/2.99      | ~ v1_funct_1(X4_60)
% 19.29/2.99      | v1_xboole_0(X1_60)
% 19.29/2.99      | v1_xboole_0(X3_60)
% 19.29/2.99      | X4_60 = X5_60 ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_5]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7088,plain,
% 19.29/2.99      ( X0_60 = X1_60
% 19.29/2.99      | r1_funct_2(X2_60,X3_60,X4_60,X5_60,X0_60,X1_60) != iProver_top
% 19.29/2.99      | v1_funct_2(X0_60,X2_60,X3_60) != iProver_top
% 19.29/2.99      | v1_funct_2(X1_60,X4_60,X5_60) != iProver_top
% 19.29/2.99      | m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(X2_60,X3_60))) != iProver_top
% 19.29/2.99      | m1_subset_1(X1_60,k1_zfmisc_1(k2_zfmisc_1(X4_60,X5_60))) != iProver_top
% 19.29/2.99      | v1_funct_1(X0_60) != iProver_top
% 19.29/2.99      | v1_funct_1(X1_60) != iProver_top
% 19.29/2.99      | v1_xboole_0(X5_60) = iProver_top
% 19.29/2.99      | v1_xboole_0(X3_60) = iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6110]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_14840,plain,
% 19.29/2.99      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3))
% 19.29/2.99      | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 19.29/2.99      | v1_funct_2(k6_partfun1(u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 19.29/2.99      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 19.29/2.99      | m1_subset_1(k6_partfun1(u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top
% 19.29/2.99      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 19.29/2.99      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top
% 19.29/2.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_14836,c_7088]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_45680,plain,
% 19.29/2.99      ( k9_tmap_1(sK3,sK4) = k6_partfun1(u1_struct_0(sK3)) ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_45678,c_56,c_57,c_58,c_60,c_62,c_190,c_197,c_2282,c_11764,
% 19.29/2.99                 c_13151,c_13152,c_13403,c_13404,c_14840]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_42,plain,
% 19.29/2.99      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
% 19.29/2.99      | ~ r1_xboole_0(u1_struct_0(X2),X1)
% 19.29/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.29/2.99      | ~ m1_pre_topc(X2,X0)
% 19.29/2.99      | ~ v2_pre_topc(X0)
% 19.29/2.99      | v2_struct_0(X0)
% 19.29/2.99      | v2_struct_0(X2)
% 19.29/2.99      | ~ l1_pre_topc(X0) ),
% 19.29/2.99      inference(cnf_transformation,[],[f121]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_47,negated_conjecture,
% 19.29/2.99      ( ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4))
% 19.29/2.99      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) ),
% 19.29/2.99      inference(cnf_transformation,[],[f133]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_651,plain,
% 19.29/2.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ r1_xboole_0(u1_struct_0(X0),X1)
% 19.29/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 19.29/2.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ m1_pre_topc(X0,X2)
% 19.29/2.99      | ~ v2_pre_topc(X2)
% 19.29/2.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 19.29/2.99      | v2_struct_0(X2)
% 19.29/2.99      | v2_struct_0(X0)
% 19.29/2.99      | ~ l1_pre_topc(X2)
% 19.29/2.99      | k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),X0) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 19.29/2.99      | k6_tmap_1(X2,X1) != k8_tmap_1(sK3,sK4)
% 19.29/2.99      | sK5 != X0 ),
% 19.29/2.99      inference(resolution_lifted,[status(thm)],[c_42,c_47]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_652,plain,
% 19.29/2.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ r1_xboole_0(u1_struct_0(sK5),X0)
% 19.29/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.29/2.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ m1_pre_topc(sK5,X1)
% 19.29/2.99      | ~ v2_pre_topc(X1)
% 19.29/2.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 19.29/2.99      | v2_struct_0(X1)
% 19.29/2.99      | v2_struct_0(sK5)
% 19.29/2.99      | ~ l1_pre_topc(X1)
% 19.29/2.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 19.29/2.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4) ),
% 19.29/2.99      inference(unflattening,[status(thm)],[c_651]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_50,negated_conjecture,
% 19.29/2.99      ( ~ v2_struct_0(sK5) ),
% 19.29/2.99      inference(cnf_transformation,[],[f130]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_656,plain,
% 19.29/2.99      ( v2_struct_0(X1)
% 19.29/2.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 19.29/2.99      | ~ v2_pre_topc(X1)
% 19.29/2.99      | ~ m1_pre_topc(sK5,X1)
% 19.29/2.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.29/2.99      | ~ r1_xboole_0(u1_struct_0(sK5),X0)
% 19.29/2.99      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ l1_pre_topc(X1)
% 19.29/2.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 19.29/2.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4) ),
% 19.29/2.99      inference(global_propositional_subsumption,[status(thm)],[c_652,c_50]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_657,plain,
% 19.29/2.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ r1_xboole_0(u1_struct_0(sK5),X0)
% 19.29/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.29/2.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ m1_pre_topc(sK5,X1)
% 19.29/2.99      | ~ v2_pre_topc(X1)
% 19.29/2.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 19.29/2.99      | v2_struct_0(X1)
% 19.29/2.99      | ~ l1_pre_topc(X1)
% 19.29/2.99      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 19.29/2.99      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4) ),
% 19.29/2.99      inference(renaming,[status(thm)],[c_656]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6064,plain,
% 19.29/2.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ r1_xboole_0(u1_struct_0(sK5),X0_60)
% 19.29/2.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
% 19.29/2.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ m1_pre_topc(sK5,X0_61)
% 19.29/2.99      | ~ v2_pre_topc(X0_61)
% 19.29/2.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 19.29/2.99      | v2_struct_0(X0_61)
% 19.29/2.99      | ~ l1_pre_topc(X0_61)
% 19.29/2.99      | k6_tmap_1(X0_61,X0_60) != k8_tmap_1(sK3,sK4)
% 19.29/2.99      | k2_tmap_1(X0_61,k6_tmap_1(X0_61,X0_60),k7_tmap_1(X0_61,X0_60),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_657]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6116,plain,
% 19.29/2.99      ( ~ r1_xboole_0(u1_struct_0(sK5),X0_60)
% 19.29/2.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61)))
% 19.29/2.99      | ~ m1_pre_topc(sK5,X0_61)
% 19.29/2.99      | ~ v2_pre_topc(X0_61)
% 19.29/2.99      | v2_struct_0(X0_61)
% 19.29/2.99      | ~ l1_pre_topc(X0_61)
% 19.29/2.99      | k6_tmap_1(X0_61,X0_60) != k8_tmap_1(sK3,sK4)
% 19.29/2.99      | k2_tmap_1(X0_61,k6_tmap_1(X0_61,X0_60),k7_tmap_1(X0_61,X0_60),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 19.29/2.99      | ~ sP0_iProver_split ),
% 19.29/2.99      inference(splitting,
% 19.29/2.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 19.29/2.99                [c_6064]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7135,plain,
% 19.29/2.99      ( k6_tmap_1(X0_61,X0_60) != k8_tmap_1(sK3,sK4)
% 19.29/2.99      | k2_tmap_1(X0_61,k6_tmap_1(X0_61,X0_60),k7_tmap_1(X0_61,X0_60),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 19.29/2.99      | r1_xboole_0(u1_struct_0(sK5),X0_60) != iProver_top
% 19.29/2.99      | m1_subset_1(X0_60,k1_zfmisc_1(u1_struct_0(X0_61))) != iProver_top
% 19.29/2.99      | m1_pre_topc(sK5,X0_61) != iProver_top
% 19.29/2.99      | v2_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | v2_struct_0(X0_61) = iProver_top
% 19.29/2.99      | l1_pre_topc(X0_61) != iProver_top
% 19.29/2.99      | sP0_iProver_split != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6116]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_9423,plain,
% 19.29/2.99      ( k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 19.29/2.99      | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 19.29/2.99      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
% 19.29/2.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.29/2.99      | m1_pre_topc(sK5,sK3) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top
% 19.29/2.99      | sP0_iProver_split != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_9421,c_7135]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_9429,plain,
% 19.29/2.99      ( k8_tmap_1(sK3,sK4) != k8_tmap_1(sK3,sK4)
% 19.29/2.99      | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 19.29/2.99      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
% 19.29/2.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.29/2.99      | m1_pre_topc(sK5,sK3) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top
% 19.29/2.99      | sP0_iProver_split != iProver_top ),
% 19.29/2.99      inference(light_normalisation,[status(thm)],[c_9423,c_9421]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_9430,plain,
% 19.29/2.99      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 19.29/2.99      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
% 19.29/2.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.29/2.99      | m1_pre_topc(sK5,sK3) != iProver_top
% 19.29/2.99      | v2_pre_topc(sK3) != iProver_top
% 19.29/2.99      | v2_struct_0(sK3) = iProver_top
% 19.29/2.99      | l1_pre_topc(sK3) != iProver_top
% 19.29/2.99      | sP0_iProver_split != iProver_top ),
% 19.29/2.99      inference(equality_resolution_simp,[status(thm)],[c_9429]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_196,plain,
% 19.29/2.99      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_0]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_1697,plain,
% 19.29/2.99      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 19.29/2.99      | ~ v2_pre_topc(X0)
% 19.29/2.99      | v2_struct_0(X0)
% 19.29/2.99      | ~ l1_pre_topc(X0)
% 19.29/2.99      | sK4 != X1
% 19.29/2.99      | sK3 != X0 ),
% 19.29/2.99      inference(resolution_lifted,[status(thm)],[c_30,c_51]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_1698,plain,
% 19.29/2.99      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ v2_pre_topc(sK3)
% 19.29/2.99      | v2_struct_0(sK3)
% 19.29/2.99      | ~ l1_pre_topc(sK3) ),
% 19.29/2.99      inference(unflattening,[status(thm)],[c_1697]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_1708,plain,
% 19.29/2.99      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 19.29/2.99      | ~ v2_pre_topc(X0)
% 19.29/2.99      | v2_struct_0(X0)
% 19.29/2.99      | ~ l1_pre_topc(X0)
% 19.29/2.99      | sK4 != X1
% 19.29/2.99      | sK3 != X0 ),
% 19.29/2.99      inference(resolution_lifted,[status(thm)],[c_29,c_51]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_1709,plain,
% 19.29/2.99      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ v2_pre_topc(sK3)
% 19.29/2.99      | v2_struct_0(sK3)
% 19.29/2.99      | ~ l1_pre_topc(sK3) ),
% 19.29/2.99      inference(unflattening,[status(thm)],[c_1708]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_1,plain,
% 19.29/2.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 19.29/2.99      inference(cnf_transformation,[],[f79]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_2248,plain,
% 19.29/2.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK5 != X1 | sK3 != X0 ),
% 19.29/2.99      inference(resolution_lifted,[status(thm)],[c_1,c_49]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_2249,plain,
% 19.29/2.99      ( l1_pre_topc(sK5) | ~ l1_pre_topc(sK3) ),
% 19.29/2.99      inference(unflattening,[status(thm)],[c_2248]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_2315,plain,
% 19.29/2.99      ( ~ v2_pre_topc(X0)
% 19.29/2.99      | v2_struct_0(X0)
% 19.29/2.99      | ~ l1_pre_topc(X0)
% 19.29/2.99      | l1_pre_topc(k8_tmap_1(X0,X1))
% 19.29/2.99      | sK4 != X1
% 19.29/2.99      | sK3 != X0 ),
% 19.29/2.99      inference(resolution_lifted,[status(thm)],[c_26,c_51]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_2316,plain,
% 19.29/2.99      ( ~ v2_pre_topc(sK3)
% 19.29/2.99      | v2_struct_0(sK3)
% 19.29/2.99      | l1_pre_topc(k8_tmap_1(sK3,sK4))
% 19.29/2.99      | ~ l1_pre_topc(sK3) ),
% 19.29/2.99      inference(unflattening,[status(thm)],[c_2315]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_2380,plain,
% 19.29/2.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK4 != X1 | sK3 != X0 ),
% 19.29/2.99      inference(resolution_lifted,[status(thm)],[c_1,c_51]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_2381,plain,
% 19.29/2.99      ( l1_pre_topc(sK4) | ~ l1_pre_topc(sK3) ),
% 19.29/2.99      inference(unflattening,[status(thm)],[c_2380]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6117,plain,
% 19.29/2.99      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 19.29/2.99      | sP0_iProver_split ),
% 19.29/2.99      inference(splitting,
% 19.29/2.99                [splitting(split),new_symbols(definition,[])],
% 19.29/2.99                [c_6064]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_19,plain,
% 19.29/2.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.29/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.29/2.99      | ~ v1_funct_1(X0)
% 19.29/2.99      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
% 19.29/2.99      | ~ l1_struct_0(X1)
% 19.29/2.99      | ~ l1_struct_0(X2)
% 19.29/2.99      | ~ l1_struct_0(X3) ),
% 19.29/2.99      inference(cnf_transformation,[],[f95]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6098,plain,
% 19.29/2.99      ( ~ v1_funct_2(X0_60,u1_struct_0(X0_61),u1_struct_0(X1_61))
% 19.29/2.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
% 19.29/2.99      | ~ v1_funct_1(X0_60)
% 19.29/2.99      | v1_funct_1(k2_tmap_1(X0_61,X1_61,X0_60,X2_61))
% 19.29/2.99      | ~ l1_struct_0(X0_61)
% 19.29/2.99      | ~ l1_struct_0(X1_61)
% 19.29/2.99      | ~ l1_struct_0(X2_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_19]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7514,plain,
% 19.29/2.99      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 19.29/2.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 19.29/2.99      | ~ l1_struct_0(k8_tmap_1(sK3,sK4))
% 19.29/2.99      | ~ l1_struct_0(sK5)
% 19.29/2.99      | ~ l1_struct_0(sK3) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_6098]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6115,plain,
% 19.29/2.99      ( ~ l1_pre_topc(X0_61) | l1_struct_0(X0_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_0]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7534,plain,
% 19.29/2.99      ( ~ l1_pre_topc(sK4) | l1_struct_0(sK4) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_6115]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7537,plain,
% 19.29/2.99      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_6115]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7824,plain,
% 19.29/2.99      ( ~ l1_pre_topc(k8_tmap_1(sK3,sK4)) | l1_struct_0(k8_tmap_1(sK3,sK4)) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_6115]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_18,plain,
% 19.29/2.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.29/2.99      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 19.29/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.29/2.99      | ~ v1_funct_1(X0)
% 19.29/2.99      | ~ l1_struct_0(X1)
% 19.29/2.99      | ~ l1_struct_0(X2)
% 19.29/2.99      | ~ l1_struct_0(X3) ),
% 19.29/2.99      inference(cnf_transformation,[],[f96]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6099,plain,
% 19.29/2.99      ( ~ v1_funct_2(X0_60,u1_struct_0(X0_61),u1_struct_0(X1_61))
% 19.29/2.99      | v1_funct_2(k2_tmap_1(X0_61,X1_61,X0_60,X2_61),u1_struct_0(X2_61),u1_struct_0(X1_61))
% 19.29/2.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
% 19.29/2.99      | ~ v1_funct_1(X0_60)
% 19.29/2.99      | ~ l1_struct_0(X0_61)
% 19.29/2.99      | ~ l1_struct_0(X1_61)
% 19.29/2.99      | ~ l1_struct_0(X2_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_18]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_8109,plain,
% 19.29/2.99      ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 19.29/2.99      | ~ l1_struct_0(k8_tmap_1(sK3,sK4))
% 19.29/2.99      | ~ l1_struct_0(sK5)
% 19.29/2.99      | ~ l1_struct_0(sK3) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_6099]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_48,negated_conjecture,
% 19.29/2.99      ( r1_tsep_1(sK4,sK5) ),
% 19.29/2.99      inference(cnf_transformation,[],[f132]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6074,negated_conjecture,
% 19.29/2.99      ( r1_tsep_1(sK4,sK5) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_48]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7124,plain,
% 19.29/2.99      ( r1_tsep_1(sK4,sK5) = iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6074]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_38,plain,
% 19.29/2.99      ( ~ r1_tsep_1(X0,X1)
% 19.29/2.99      | r1_tsep_1(X1,X0)
% 19.29/2.99      | ~ l1_struct_0(X0)
% 19.29/2.99      | ~ l1_struct_0(X1) ),
% 19.29/2.99      inference(cnf_transformation,[],[f116]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6082,plain,
% 19.29/2.99      ( ~ r1_tsep_1(X0_61,X1_61)
% 19.29/2.99      | r1_tsep_1(X1_61,X0_61)
% 19.29/2.99      | ~ l1_struct_0(X0_61)
% 19.29/2.99      | ~ l1_struct_0(X1_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_38]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_7116,plain,
% 19.29/2.99      ( r1_tsep_1(X0_61,X1_61) != iProver_top
% 19.29/2.99      | r1_tsep_1(X1_61,X0_61) = iProver_top
% 19.29/2.99      | l1_struct_0(X0_61) != iProver_top
% 19.29/2.99      | l1_struct_0(X1_61) != iProver_top ),
% 19.29/2.99      inference(predicate_to_equality,[status(thm)],[c_6082]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_8179,plain,
% 19.29/2.99      ( r1_tsep_1(sK5,sK4) = iProver_top
% 19.29/2.99      | l1_struct_0(sK5) != iProver_top
% 19.29/2.99      | l1_struct_0(sK4) != iProver_top ),
% 19.29/2.99      inference(superposition,[status(thm)],[c_7124,c_7116]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_8180,plain,
% 19.29/2.99      ( r1_tsep_1(sK5,sK4) | ~ l1_struct_0(sK5) | ~ l1_struct_0(sK4) ),
% 19.29/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_8179]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_17,plain,
% 19.29/2.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.29/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.29/2.99      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 19.29/2.99      | ~ v1_funct_1(X0)
% 19.29/2.99      | ~ l1_struct_0(X1)
% 19.29/2.99      | ~ l1_struct_0(X2)
% 19.29/2.99      | ~ l1_struct_0(X3) ),
% 19.29/2.99      inference(cnf_transformation,[],[f97]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6100,plain,
% 19.29/2.99      ( ~ v1_funct_2(X0_60,u1_struct_0(X0_61),u1_struct_0(X1_61))
% 19.29/2.99      | ~ m1_subset_1(X0_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X1_61))))
% 19.29/2.99      | m1_subset_1(k2_tmap_1(X0_61,X1_61,X0_60,X2_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_61),u1_struct_0(X1_61))))
% 19.29/2.99      | ~ v1_funct_1(X0_60)
% 19.29/2.99      | ~ l1_struct_0(X0_61)
% 19.29/2.99      | ~ l1_struct_0(X1_61)
% 19.29/2.99      | ~ l1_struct_0(X2_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_17]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_8315,plain,
% 19.29/2.99      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 19.29/2.99      | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 19.29/2.99      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 19.29/2.99      | ~ l1_struct_0(k8_tmap_1(sK3,sK4))
% 19.29/2.99      | ~ l1_struct_0(sK5)
% 19.29/2.99      | ~ l1_struct_0(sK3) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_6100]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_9432,plain,
% 19.29/2.99      ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
% 19.29/2.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.29/2.99      | ~ m1_pre_topc(sK5,sK3)
% 19.29/2.99      | ~ v2_pre_topc(sK3)
% 19.29/2.99      | v2_struct_0(sK3)
% 19.29/2.99      | ~ l1_pre_topc(sK3)
% 19.29/2.99      | ~ sP0_iProver_split
% 19.29/2.99      | k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
% 19.29/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_9430]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_16,plain,
% 19.29/2.99      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 19.29/2.99      | ~ r1_tsep_1(X0,X1)
% 19.29/2.99      | ~ l1_struct_0(X0)
% 19.29/2.99      | ~ l1_struct_0(X1) ),
% 19.29/2.99      inference(cnf_transformation,[],[f93]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_6101,plain,
% 19.29/2.99      ( r1_xboole_0(u1_struct_0(X0_61),u1_struct_0(X1_61))
% 19.29/2.99      | ~ r1_tsep_1(X0_61,X1_61)
% 19.29/2.99      | ~ l1_struct_0(X0_61)
% 19.29/2.99      | ~ l1_struct_0(X1_61) ),
% 19.29/2.99      inference(subtyping,[status(esa)],[c_16]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_9530,plain,
% 19.29/2.99      ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
% 19.29/2.99      | ~ r1_tsep_1(sK5,sK4)
% 19.29/2.99      | ~ l1_struct_0(sK5)
% 19.29/2.99      | ~ l1_struct_0(sK4) ),
% 19.29/2.99      inference(instantiation,[status(thm)],[c_6101]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_10059,plain,
% 19.29/2.99      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
% 19.29/2.99      inference(global_propositional_subsumption,
% 19.29/2.99                [status(thm)],
% 19.29/2.99                [c_9430,c_55,c_54,c_53,c_49,c_196,c_1698,c_1709,c_2249,
% 19.29/2.99                 c_2268,c_2281,c_2316,c_2381,c_6117,c_7514,c_7534,c_7537,
% 19.29/2.99                 c_7824,c_8109,c_8180,c_8315,c_9432,c_9530]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_11787,plain,
% 19.29/2.99      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
% 19.29/2.99      inference(demodulation,[status(thm)],[c_11784,c_10059]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_45688,plain,
% 19.29/2.99      ( k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k6_partfun1(u1_struct_0(sK3)),sK5) ),
% 19.29/2.99      inference(demodulation,[status(thm)],[c_45680,c_11787]) ).
% 19.29/2.99  
% 19.29/2.99  cnf(c_45690,plain,
% 19.29/2.99      ( $false ),
% 19.29/2.99      inference(equality_resolution_simp,[status(thm)],[c_45688]) ).
% 19.29/2.99  
% 19.29/2.99  
% 19.29/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.29/2.99  
% 19.29/2.99  ------                               Statistics
% 19.29/2.99  
% 19.29/2.99  ------ General
% 19.29/2.99  
% 19.29/2.99  abstr_ref_over_cycles:                  0
% 19.29/2.99  abstr_ref_under_cycles:                 0
% 19.29/2.99  gc_basic_clause_elim:                   0
% 19.29/2.99  forced_gc_time:                         0
% 19.29/2.99  parsing_time:                           0.015
% 19.29/2.99  unif_index_cands_time:                  0.
% 19.29/2.99  unif_index_add_time:                    0.
% 19.29/2.99  orderings_time:                         0.
% 19.29/2.99  out_proof_time:                         0.023
% 19.29/2.99  total_time:                             2.145
% 19.29/2.99  num_of_symbols:                         71
% 19.29/2.99  num_of_terms:                           51767
% 19.29/2.99  
% 19.29/2.99  ------ Preprocessing
% 19.29/2.99  
% 19.29/2.99  num_of_splits:                          1
% 19.29/2.99  num_of_split_atoms:                     1
% 19.29/2.99  num_of_reused_defs:                     0
% 19.29/2.99  num_eq_ax_congr_red:                    37
% 19.29/2.99  num_of_sem_filtered_clauses:            5
% 19.29/2.99  num_of_subtypes:                        4
% 19.29/2.99  monotx_restored_types:                  0
% 19.29/2.99  sat_num_of_epr_types:                   0
% 19.29/2.99  sat_num_of_non_cyclic_types:            0
% 19.29/2.99  sat_guarded_non_collapsed_types:        2
% 19.29/2.99  num_pure_diseq_elim:                    0
% 19.29/2.99  simp_replaced_by:                       0
% 19.29/2.99  res_preprocessed:                       272
% 19.29/2.99  prep_upred:                             0
% 19.29/2.99  prep_unflattend:                        372
% 19.29/2.99  smt_new_axioms:                         0
% 19.29/2.99  pred_elim_cands:                        13
% 19.29/2.99  pred_elim:                              1
% 19.29/2.99  pred_elim_cl:                           1
% 19.29/2.99  pred_elim_cycles:                       10
% 19.29/2.99  merged_defs:                            0
% 19.29/2.99  merged_defs_ncl:                        0
% 19.29/2.99  bin_hyper_res:                          0
% 19.29/2.99  prep_cycles:                            4
% 19.29/2.99  pred_elim_time:                         0.119
% 19.29/2.99  splitting_time:                         0.
% 19.29/2.99  sem_filter_time:                        0.
% 19.29/2.99  monotx_time:                            0.
% 19.29/2.99  subtype_inf_time:                       0.001
% 19.29/2.99  
% 19.29/2.99  ------ Problem properties
% 19.29/2.99  
% 19.29/2.99  clauses:                                54
% 19.29/2.99  conjectures:                            8
% 19.29/2.99  epr:                                    12
% 19.29/2.99  horn:                                   24
% 19.29/2.99  ground:                                 10
% 19.29/2.99  unary:                                  8
% 19.29/2.99  binary:                                 3
% 19.29/2.99  lits:                                   271
% 19.29/2.99  lits_eq:                                18
% 19.29/2.99  fd_pure:                                0
% 19.29/2.99  fd_pseudo:                              0
% 19.29/2.99  fd_cond:                                0
% 19.29/2.99  fd_pseudo_cond:                         7
% 19.29/2.99  ac_symbols:                             0
% 19.29/2.99  
% 19.29/2.99  ------ Propositional Solver
% 19.29/2.99  
% 19.29/2.99  prop_solver_calls:                      34
% 19.29/2.99  prop_fast_solver_calls:                 7047
% 19.29/2.99  smt_solver_calls:                       0
% 19.29/2.99  smt_fast_solver_calls:                  0
% 19.29/2.99  prop_num_of_clauses:                    17004
% 19.29/2.99  prop_preprocess_simplified:             26961
% 19.29/2.99  prop_fo_subsumed:                       1091
% 19.29/2.99  prop_solver_time:                       0.
% 19.29/2.99  smt_solver_time:                        0.
% 19.29/2.99  smt_fast_solver_time:                   0.
% 19.29/2.99  prop_fast_solver_time:                  0.
% 19.29/2.99  prop_unsat_core_time:                   0.
% 19.29/2.99  
% 19.29/2.99  ------ QBF
% 19.29/2.99  
% 19.29/2.99  qbf_q_res:                              0
% 19.29/2.99  qbf_num_tautologies:                    0
% 19.29/2.99  qbf_prep_cycles:                        0
% 19.29/2.99  
% 19.29/2.99  ------ BMC1
% 19.29/2.99  
% 19.29/2.99  bmc1_current_bound:                     -1
% 19.29/2.99  bmc1_last_solved_bound:                 -1
% 19.29/2.99  bmc1_unsat_core_size:                   -1
% 19.29/2.99  bmc1_unsat_core_parents_size:           -1
% 19.29/2.99  bmc1_merge_next_fun:                    0
% 19.29/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.29/2.99  
% 19.29/2.99  ------ Instantiation
% 19.29/2.99  
% 19.29/2.99  inst_num_of_clauses:                    3502
% 19.29/2.99  inst_num_in_passive:                    469
% 19.29/2.99  inst_num_in_active:                     1887
% 19.29/2.99  inst_num_in_unprocessed:                1146
% 19.29/2.99  inst_num_of_loops:                      1960
% 19.29/2.99  inst_num_of_learning_restarts:          0
% 19.29/2.99  inst_num_moves_active_passive:          68
% 19.29/2.99  inst_lit_activity:                      0
% 19.29/2.99  inst_lit_activity_moves:                0
% 19.29/2.99  inst_num_tautologies:                   0
% 19.29/2.99  inst_num_prop_implied:                  0
% 19.29/2.99  inst_num_existing_simplified:           0
% 19.29/2.99  inst_num_eq_res_simplified:             0
% 19.29/2.99  inst_num_child_elim:                    0
% 19.29/2.99  inst_num_of_dismatching_blockings:      6177
% 19.29/2.99  inst_num_of_non_proper_insts:           6080
% 19.29/2.99  inst_num_of_duplicates:                 0
% 19.29/2.99  inst_inst_num_from_inst_to_res:         0
% 19.29/2.99  inst_dismatching_checking_time:         0.
% 19.29/2.99  
% 19.29/2.99  ------ Resolution
% 19.29/2.99  
% 19.29/2.99  res_num_of_clauses:                     0
% 19.29/2.99  res_num_in_passive:                     0
% 19.29/2.99  res_num_in_active:                      0
% 19.29/2.99  res_num_of_loops:                       276
% 19.29/2.99  res_forward_subset_subsumed:            85
% 19.29/2.99  res_backward_subset_subsumed:           0
% 19.29/2.99  res_forward_subsumed:                   2
% 19.29/2.99  res_backward_subsumed:                  0
% 19.29/2.99  res_forward_subsumption_resolution:     16
% 19.29/2.99  res_backward_subsumption_resolution:    10
% 19.29/2.99  res_clause_to_clause_subsumption:       9205
% 19.29/2.99  res_orphan_elimination:                 0
% 19.29/2.99  res_tautology_del:                      488
% 19.29/2.99  res_num_eq_res_simplified:              0
% 19.29/2.99  res_num_sel_changes:                    0
% 19.29/2.99  res_moves_from_active_to_pass:          0
% 19.29/2.99  
% 19.29/2.99  ------ Superposition
% 19.29/2.99  
% 19.29/2.99  sup_time_total:                         0.
% 19.29/2.99  sup_time_generating:                    0.
% 19.29/2.99  sup_time_sim_full:                      0.
% 19.29/2.99  sup_time_sim_immed:                     0.
% 19.29/2.99  
% 19.29/2.99  sup_num_of_clauses:                     1963
% 19.29/2.99  sup_num_in_active:                      321
% 19.29/2.99  sup_num_in_passive:                     1642
% 19.29/2.99  sup_num_of_loops:                       390
% 19.29/2.99  sup_fw_superposition:                   766
% 19.29/2.99  sup_bw_superposition:                   1814
% 19.29/2.99  sup_immediate_simplified:               853
% 19.29/2.99  sup_given_eliminated:                   21
% 19.29/2.99  comparisons_done:                       0
% 19.29/2.99  comparisons_avoided:                    364
% 19.29/2.99  
% 19.29/2.99  ------ Simplifications
% 19.29/2.99  
% 19.29/2.99  
% 19.29/2.99  sim_fw_subset_subsumed:                 141
% 19.29/2.99  sim_bw_subset_subsumed:                 42
% 19.29/2.99  sim_fw_subsumed:                        221
% 19.29/2.99  sim_bw_subsumed:                        76
% 19.29/2.99  sim_fw_subsumption_res:                 0
% 19.29/2.99  sim_bw_subsumption_res:                 0
% 19.29/2.99  sim_tautology_del:                      51
% 19.29/2.99  sim_eq_tautology_del:                   15
% 19.29/2.99  sim_eq_res_simp:                        2
% 19.29/2.99  sim_fw_demodulated:                     119
% 19.29/2.99  sim_bw_demodulated:                     36
% 19.29/2.99  sim_light_normalised:                   831
% 19.29/2.99  sim_joinable_taut:                      0
% 19.29/2.99  sim_joinable_simp:                      0
% 19.29/2.99  sim_ac_normalised:                      0
% 19.29/2.99  sim_smt_subsumption:                    0
% 19.29/2.99  
%------------------------------------------------------------------------------
