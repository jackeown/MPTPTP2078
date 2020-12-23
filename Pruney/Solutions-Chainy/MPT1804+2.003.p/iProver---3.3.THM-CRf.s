%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:11 EST 2020

% Result     : Theorem 11.72s
% Output     : CNFRefutation 11.72s
% Verified   : 
% Statistics : Number of formulae       :  284 (1423 expanded)
%              Number of clauses        :  180 ( 460 expanded)
%              Number of leaves         :   29 ( 368 expanded)
%              Depth                    :   23
%              Number of atoms          : 1496 (11760 expanded)
%              Number of equality atoms :  415 ( 836 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f73,plain,(
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

fof(f72,plain,(
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

fof(f71,plain,
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

fof(f74,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f58,f73,f72,f71])).

fof(f121,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f64])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f65])).

fof(f127,plain,(
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
    inference(equality_resolution,[],[f82])).

fof(f128,plain,(
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
    inference(equality_resolution,[],[f127])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1))
        & ~ v2_struct_0(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f100,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f118,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f119,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f123,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f124,plain,(
    r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f74])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f125,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f74])).

fof(f122,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f74])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2)))
        & u1_struct_0(X1) = sK2(X0,X1,X2)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f67,f68])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f69])).

fof(f129,plain,(
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
    inference(equality_resolution,[],[f86])).

fof(f130,plain,(
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
    inference(equality_resolution,[],[f129])).

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

fof(f28,plain,(
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
    inference(flattening,[],[f28])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f108,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f115,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_46,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1869,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_46])).

cnf(c_2841,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1869])).

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
    inference(cnf_transformation,[],[f128])).

cnf(c_39,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_30,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_29,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_325,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_39,c_30,c_29,c_23])).

cnf(c_326,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_1863,plain,
    ( ~ m1_pre_topc(X0_60,X1_60)
    | ~ v2_pre_topc(X1_60)
    | v2_struct_0(X1_60)
    | ~ l1_pre_topc(X1_60)
    | k6_tmap_1(X1_60,u1_struct_0(X0_60)) = k8_tmap_1(X1_60,X0_60) ),
    inference(subtyping,[status(esa)],[c_326])).

cnf(c_2847,plain,
    ( k6_tmap_1(X0_60,u1_struct_0(X1_60)) = k8_tmap_1(X0_60,X1_60)
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1863])).

cnf(c_8621,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_2847])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_51,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_52,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_53,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_8848,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8621,c_51,c_52,c_53])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1891,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
    | m1_subset_1(k7_tmap_1(X0_60,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_59)))))
    | ~ v2_pre_topc(X0_60)
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2819,plain,
    ( m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
    | m1_subset_1(k7_tmap_1(X0_60,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_59))))) = iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1891])).

cnf(c_8857,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8848,c_2819])).

cnf(c_55,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_1875,plain,
    ( m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(X1_60)))
    | ~ m1_pre_topc(X0_60,X1_60)
    | ~ l1_pre_topc(X1_60) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_7131,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0_60)))
    | ~ m1_pre_topc(sK4,X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(instantiation,[status(thm)],[c_1875])).

cnf(c_7132,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0_60))) = iProver_top
    | m1_pre_topc(sK4,X0_60) != iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7131])).

cnf(c_7134,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7132])).

cnf(c_9046,plain,
    ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8857,c_51,c_52,c_53,c_55,c_7134])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1892,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60))))
    | ~ v1_funct_1(X0_59)
    | v1_funct_1(k2_tmap_1(X0_60,X1_60,X0_59,X2_60))
    | ~ l1_struct_0(X0_60)
    | ~ l1_struct_0(X1_60)
    | ~ l1_struct_0(X2_60) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2818,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_60,X1_60,X0_59,X2_60)) = iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(X1_60) != iProver_top
    | l1_struct_0(X2_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1892])).

cnf(c_9050,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),X0_60)) = iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9046,c_2818])).

cnf(c_44,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_166,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_168,plain,
    ( v2_struct_0(sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_173,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_175,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_1922,plain,
    ( X0_60 != X1_60
    | u1_struct_0(X0_60) = u1_struct_0(X1_60) ),
    theory(equality)).

cnf(c_1944,plain,
    ( sK3 != sK3
    | u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1922])).

cnf(c_1914,plain,
    ( X0_60 = X0_60 ),
    theory(equality)).

cnf(c_1966,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1914])).

cnf(c_1909,plain,
    ( ~ l1_pre_topc(X0_60)
    | l1_struct_0(X0_60) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3193,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1909])).

cnf(c_3196,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1909])).

cnf(c_1871,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(subtyping,[status(esa)],[c_44])).

cnf(c_2839,plain,
    ( m1_pre_topc(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1871])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1908,plain,
    ( ~ m1_pre_topc(X0_60,X1_60)
    | ~ l1_pre_topc(X1_60)
    | l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2802,plain,
    ( m1_pre_topc(X0_60,X1_60) != iProver_top
    | l1_pre_topc(X1_60) != iProver_top
    | l1_pre_topc(X0_60) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1908])).

cnf(c_3551,plain,
    ( l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2839,c_2802])).

cnf(c_3555,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3551])).

cnf(c_3552,plain,
    ( l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_2802])).

cnf(c_3556,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3552])).

cnf(c_43,negated_conjecture,
    ( r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1872,negated_conjecture,
    ( r1_tsep_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_43])).

cnf(c_2838,plain,
    ( r1_tsep_1(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1872])).

cnf(c_32,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1881,plain,
    ( ~ r1_tsep_1(X0_60,X1_60)
    | r1_tsep_1(X1_60,X0_60)
    | ~ l1_struct_0(X0_60)
    | ~ l1_struct_0(X1_60) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2829,plain,
    ( r1_tsep_1(X0_60,X1_60) != iProver_top
    | r1_tsep_1(X1_60,X0_60) = iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(X1_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_3880,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2838,c_2829])).

cnf(c_3881,plain,
    ( r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3880])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1883,plain,
    ( ~ m1_pre_topc(X0_60,X1_60)
    | ~ v2_pre_topc(X1_60)
    | v1_funct_1(k9_tmap_1(X1_60,X0_60))
    | v2_struct_0(X1_60)
    | ~ l1_pre_topc(X1_60) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3931,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v1_funct_1(k9_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1883])).

cnf(c_3932,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3931])).

cnf(c_4557,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1914])).

cnf(c_16,plain,
    ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1895,plain,
    ( r1_xboole_0(u1_struct_0(X0_60),u1_struct_0(X1_60))
    | ~ r1_tsep_1(X0_60,X1_60)
    | ~ l1_struct_0(X0_60)
    | ~ l1_struct_0(X1_60) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_5063,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_27,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1884,plain,
    ( v1_funct_2(k9_tmap_1(X0_60,X1_60),u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)))
    | ~ m1_pre_topc(X1_60,X0_60)
    | ~ v2_pre_topc(X0_60)
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_6453,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1884])).

cnf(c_6454,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6453])).

cnf(c_26,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1885,plain,
    ( m1_subset_1(k9_tmap_1(X0_60,X1_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)))))
    | ~ m1_pre_topc(X1_60,X0_60)
    | ~ v2_pre_topc(X0_60)
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2825,plain,
    ( m1_subset_1(k9_tmap_1(X0_60,X1_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60))))) = iProver_top
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1893,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60))
    | v1_funct_2(k2_tmap_1(X0_60,X1_60,X0_59,X2_60),u1_struct_0(X2_60),u1_struct_0(X1_60))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60))))
    | ~ v1_funct_1(X0_59)
    | ~ l1_struct_0(X0_60)
    | ~ l1_struct_0(X1_60)
    | ~ l1_struct_0(X2_60) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2817,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_60,X1_60,X0_59,X2_60),u1_struct_0(X2_60),u1_struct_0(X1_60)) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60)))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(X1_60) != iProver_top
    | l1_struct_0(X2_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1893])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1894,plain,
    ( ~ v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60))))
    | m1_subset_1(k2_tmap_1(X0_60,X1_60,X0_59,X2_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_60),u1_struct_0(X1_60))))
    | ~ v1_funct_1(X0_59)
    | ~ l1_struct_0(X0_60)
    | ~ l1_struct_0(X1_60)
    | ~ l1_struct_0(X2_60) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2816,plain,
    ( v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60)) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_60,X1_60,X0_59,X2_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_60),u1_struct_0(X1_60)))) = iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | l1_struct_0(X0_60) != iProver_top
    | l1_struct_0(X1_60) != iProver_top
    | l1_struct_0(X2_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_36,plain,
    ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
    | ~ r1_xboole_0(u1_struct_0(X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X2,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_42,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_566,plain,
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
    inference(resolution_lifted,[status(thm)],[c_36,c_42])).

cnf(c_567,plain,
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
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_571,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_45])).

cnf(c_572,plain,
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
    inference(renaming,[status(thm)],[c_571])).

cnf(c_1862,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ r1_xboole_0(u1_struct_0(sK5),X0_59)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_pre_topc(sK5,X0_60)
    | ~ v2_pre_topc(X0_60)
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60)
    | k6_tmap_1(X0_60,X0_59) != k8_tmap_1(sK3,sK4)
    | k2_tmap_1(X0_60,k6_tmap_1(X0_60,X0_59),k7_tmap_1(X0_60,X0_59),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_572])).

cnf(c_1911,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1862])).

cnf(c_2848,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1911])).

cnf(c_6492,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | l1_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2816,c_2848])).

cnf(c_3173,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
    | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
    | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
    | ~ l1_struct_0(k8_tmap_1(sK3,sK4))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_3174,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) = iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | l1_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3173])).

cnf(c_3197,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3196])).

cnf(c_3618,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK3,X0_60))
    | l1_struct_0(k8_tmap_1(sK3,X0_60)) ),
    inference(instantiation,[status(thm)],[c_1909])).

cnf(c_4263,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
    | l1_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3618])).

cnf(c_4264,plain,
    ( l1_pre_topc(k8_tmap_1(sK3,sK4)) != iProver_top
    | l1_struct_0(k8_tmap_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4263])).

cnf(c_1888,plain,
    ( ~ m1_pre_topc(X0_60,X1_60)
    | ~ v2_pre_topc(X1_60)
    | v2_struct_0(X1_60)
    | ~ l1_pre_topc(X1_60)
    | l1_pre_topc(k8_tmap_1(X1_60,X0_60)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_5296,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | l1_pre_topc(k8_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1888])).

cnf(c_5297,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5296])).

cnf(c_6623,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6492,c_51,c_52,c_53,c_55,c_175,c_3174,c_3197,c_3551,c_3932,c_4264,c_5297,c_6454])).

cnf(c_6624,plain,
    ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_6623])).

cnf(c_6627,plain,
    ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | l1_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2817,c_6624])).

cnf(c_6826,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6627,c_51,c_52,c_53,c_55,c_175,c_3197,c_3551,c_3932,c_4264,c_5297,c_6454])).

cnf(c_6830,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2825,c_6826])).

cnf(c_6831,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6830])).

cnf(c_7133,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_7131])).

cnf(c_8321,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_8322,plain,
    ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8321])).

cnf(c_21,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1890,plain,
    ( v1_funct_2(k7_tmap_1(X0_60,X0_59),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_59)))
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
    | ~ v2_pre_topc(X0_60)
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2820,plain,
    ( v1_funct_2(k7_tmap_1(X0_60,X0_59),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_59))) = iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1890])).

cnf(c_8858,plain,
    ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8848,c_2820])).

cnf(c_1910,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),X0_59)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
    | ~ m1_pre_topc(sK5,X0_60)
    | ~ v2_pre_topc(X0_60)
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60)
    | k6_tmap_1(X0_60,X0_59) != k8_tmap_1(sK3,sK4)
    | k2_tmap_1(X0_60,k6_tmap_1(X0_60,X0_59),k7_tmap_1(X0_60,X0_59),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1862])).

cnf(c_9829,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0_60)))
    | ~ m1_pre_topc(sK5,X0_60)
    | ~ v2_pre_topc(X0_60)
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60)
    | ~ sP0_iProver_split
    | k6_tmap_1(X0_60,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | k2_tmap_1(X0_60,k6_tmap_1(X0_60,u1_struct_0(sK4)),k7_tmap_1(X0_60,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_1910])).

cnf(c_9831,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK5,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ sP0_iProver_split
    | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_9829])).

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
    inference(cnf_transformation,[],[f130])).

cnf(c_315,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_27,c_26])).

cnf(c_1864,plain,
    ( r1_funct_2(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))),k9_tmap_1(X0_60,X1_60),k7_tmap_1(X0_60,u1_struct_0(X1_60)))
    | ~ m1_subset_1(u1_struct_0(X1_60),k1_zfmisc_1(u1_struct_0(X0_60)))
    | ~ m1_pre_topc(X1_60,X0_60)
    | ~ v2_pre_topc(X0_60)
    | ~ v1_funct_1(k9_tmap_1(X0_60,X1_60))
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_2846,plain,
    ( r1_funct_2(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))),k9_tmap_1(X0_60,X1_60),k7_tmap_1(X0_60,u1_struct_0(X1_60))) = iProver_top
    | m1_subset_1(u1_struct_0(X1_60),k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v1_funct_1(k9_tmap_1(X0_60,X1_60)) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1864])).

cnf(c_8860,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8848,c_2846])).

cnf(c_10008,plain,
    ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8860,c_51,c_52,c_53,c_55,c_3932,c_7134])).

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
    inference(cnf_transformation,[],[f79])).

cnf(c_1904,plain,
    ( ~ r1_funct_2(X0_59,X1_59,X2_59,X3_59,X4_59,X5_59)
    | ~ v1_funct_2(X5_59,X2_59,X3_59)
    | ~ v1_funct_2(X4_59,X0_59,X1_59)
    | ~ m1_subset_1(X5_59,k1_zfmisc_1(k2_zfmisc_1(X2_59,X3_59)))
    | ~ m1_subset_1(X4_59,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
    | ~ v1_funct_1(X5_59)
    | ~ v1_funct_1(X4_59)
    | v1_xboole_0(X1_59)
    | v1_xboole_0(X3_59)
    | X4_59 = X5_59 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2806,plain,
    ( X0_59 = X1_59
    | r1_funct_2(X2_59,X3_59,X4_59,X5_59,X0_59,X1_59) != iProver_top
    | v1_funct_2(X0_59,X2_59,X3_59) != iProver_top
    | v1_funct_2(X1_59,X4_59,X5_59) != iProver_top
    | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X2_59,X3_59))) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(X4_59,X5_59))) != iProver_top
    | v1_funct_1(X0_59) != iProver_top
    | v1_funct_1(X1_59) != iProver_top
    | v1_xboole_0(X5_59) = iProver_top
    | v1_xboole_0(X3_59) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1904])).

cnf(c_10012,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
    | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
    | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10008,c_2806])).

cnf(c_2835,plain,
    ( m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(X1_60))) = iProver_top
    | m1_pre_topc(X0_60,X1_60) != iProver_top
    | l1_pre_topc(X1_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1875])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1879,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
    | ~ v2_pre_topc(X0_60)
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60)
    | u1_struct_0(k6_tmap_1(X0_60,X0_59)) = u1_struct_0(X0_60) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_2831,plain,
    ( u1_struct_0(k6_tmap_1(X0_60,X0_59)) = u1_struct_0(X0_60)
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1879])).

cnf(c_4892,plain,
    ( u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))) = u1_struct_0(X0_60)
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(superposition,[status(thm)],[c_2835,c_2831])).

cnf(c_12637,plain,
    ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3)
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_4892])).

cnf(c_12650,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3)
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12637,c_8848])).

cnf(c_1940,plain,
    ( X0_60 != X1_60
    | X2_60 != X3_60
    | X4_60 != X5_60
    | X0_59 != X1_59
    | k2_tmap_1(X0_60,X2_60,X0_59,X4_60) = k2_tmap_1(X1_60,X3_60,X1_59,X5_60) ),
    theory(equality)).

cnf(c_17657,plain,
    ( X0_60 != sK3
    | k6_tmap_1(X0_60,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | sK5 != sK5
    | k2_tmap_1(X0_60,k6_tmap_1(X0_60,u1_struct_0(sK4)),k7_tmap_1(X0_60,u1_struct_0(sK4)),sK5) = k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | k7_tmap_1(X0_60,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1940])).

cnf(c_17658,plain,
    ( k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
    | sK5 != sK5
    | sK3 != sK3
    | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) = k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
    | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_17657])).

cnf(c_1923,plain,
    ( ~ v1_xboole_0(X0_59)
    | v1_xboole_0(X1_59)
    | X1_59 != X0_59 ),
    theory(equality)).

cnf(c_3182,plain,
    ( ~ v1_xboole_0(X0_59)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK3) != X0_59 ),
    inference(instantiation,[status(thm)],[c_1923])).

cnf(c_18005,plain,
    ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3182])).

cnf(c_18006,plain,
    ( u1_struct_0(sK3) != u1_struct_0(k8_tmap_1(sK3,sK4))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18005])).

cnf(c_1917,plain,
    ( X0_59 != X1_59
    | X2_59 != X1_59
    | X2_59 = X0_59 ),
    theory(equality)).

cnf(c_3639,plain,
    ( X0_59 != X1_59
    | u1_struct_0(sK3) != X1_59
    | u1_struct_0(sK3) = X0_59 ),
    inference(instantiation,[status(thm)],[c_1917])).

cnf(c_3964,plain,
    ( X0_59 != u1_struct_0(sK3)
    | u1_struct_0(sK3) = X0_59
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3639])).

cnf(c_4569,plain,
    ( u1_struct_0(X0_60) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = u1_struct_0(X0_60)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3964])).

cnf(c_19821,plain,
    ( u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = u1_struct_0(k8_tmap_1(sK3,sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4569])).

cnf(c_28770,plain,
    ( v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9050,c_50,c_51,c_49,c_52,c_48,c_53,c_46,c_55,c_44,c_168,c_175,c_1944,c_1966,c_3193,c_3196,c_3555,c_3556,c_3881,c_3932,c_4557,c_5063,c_6454,c_6831,c_7133,c_7134,c_8322,c_8621,c_8857,c_8858,c_9831,c_10012,c_12650,c_17658,c_18006,c_19821])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1903,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
    | ~ v2_pre_topc(X0_60)
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60)
    | k7_tmap_1(X0_60,X0_59) = k6_partfun1(u1_struct_0(X0_60)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2807,plain,
    ( k7_tmap_1(X0_60,X0_59) = k6_partfun1(u1_struct_0(X0_60))
    | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_4805,plain,
    ( k7_tmap_1(X0_60,u1_struct_0(X1_60)) = k6_partfun1(u1_struct_0(X0_60))
    | m1_pre_topc(X1_60,X0_60) != iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(superposition,[status(thm)],[c_2835,c_2807])).

cnf(c_11250,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3))
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_4805])).

cnf(c_11444,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11250,c_51,c_52,c_53])).

cnf(c_28774,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28770,c_11444])).

cnf(c_1866,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_49])).

cnf(c_2844,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1866])).

cnf(c_40,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1874,plain,
    ( m1_pre_topc(X0_60,X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_2836,plain,
    ( m1_pre_topc(X0_60,X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1874])).

cnf(c_11251,plain,
    ( k7_tmap_1(X0_60,u1_struct_0(X0_60)) = k6_partfun1(u1_struct_0(X0_60))
    | v2_pre_topc(X0_60) != iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(superposition,[status(thm)],[c_2836,c_4805])).

cnf(c_11490,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3))
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2844,c_11251])).

cnf(c_62,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_65,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_2937,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,X0_59) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_3326,plain,
    ( ~ m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(X0_60)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2937])).

cnf(c_3328,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3326])).

cnf(c_11563,plain,
    ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11490,c_50,c_49,c_48,c_62,c_65,c_3328])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1889,plain,
    ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
    | ~ v2_pre_topc(X0_60)
    | v1_funct_1(k7_tmap_1(X0_60,X0_59))
    | v2_struct_0(X0_60)
    | ~ l1_pre_topc(X0_60) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2821,plain,
    ( m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
    | v2_pre_topc(X0_60) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_60,X0_59)) = iProver_top
    | v2_struct_0(X0_60) = iProver_top
    | l1_pre_topc(X0_60) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1889])).

cnf(c_4810,plain,
    ( m1_pre_topc(X0_60,X1_60) != iProver_top
    | v2_pre_topc(X1_60) != iProver_top
    | v1_funct_1(k7_tmap_1(X1_60,u1_struct_0(X0_60))) = iProver_top
    | v2_struct_0(X1_60) = iProver_top
    | l1_pre_topc(X1_60) != iProver_top ),
    inference(superposition,[status(thm)],[c_2835,c_2821])).

cnf(c_12099,plain,
    ( m1_pre_topc(sK3,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11563,c_4810])).

cnf(c_61,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_63,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28774,c_12099,c_63,c_53,c_52,c_51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.72/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.72/2.00  
% 11.72/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.72/2.00  
% 11.72/2.00  ------  iProver source info
% 11.72/2.00  
% 11.72/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.72/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.72/2.00  git: non_committed_changes: false
% 11.72/2.00  git: last_make_outside_of_git: false
% 11.72/2.00  
% 11.72/2.00  ------ 
% 11.72/2.00  
% 11.72/2.00  ------ Input Options
% 11.72/2.00  
% 11.72/2.00  --out_options                           all
% 11.72/2.00  --tptp_safe_out                         true
% 11.72/2.00  --problem_path                          ""
% 11.72/2.00  --include_path                          ""
% 11.72/2.00  --clausifier                            res/vclausify_rel
% 11.72/2.00  --clausifier_options                    ""
% 11.72/2.00  --stdin                                 false
% 11.72/2.00  --stats_out                             all
% 11.72/2.00  
% 11.72/2.00  ------ General Options
% 11.72/2.00  
% 11.72/2.00  --fof                                   false
% 11.72/2.00  --time_out_real                         305.
% 11.72/2.00  --time_out_virtual                      -1.
% 11.72/2.00  --symbol_type_check                     false
% 11.72/2.00  --clausify_out                          false
% 11.72/2.00  --sig_cnt_out                           false
% 11.72/2.00  --trig_cnt_out                          false
% 11.72/2.00  --trig_cnt_out_tolerance                1.
% 11.72/2.00  --trig_cnt_out_sk_spl                   false
% 11.72/2.00  --abstr_cl_out                          false
% 11.72/2.00  
% 11.72/2.00  ------ Global Options
% 11.72/2.00  
% 11.72/2.00  --schedule                              default
% 11.72/2.00  --add_important_lit                     false
% 11.72/2.00  --prop_solver_per_cl                    1000
% 11.72/2.00  --min_unsat_core                        false
% 11.72/2.00  --soft_assumptions                      false
% 11.72/2.00  --soft_lemma_size                       3
% 11.72/2.00  --prop_impl_unit_size                   0
% 11.72/2.00  --prop_impl_unit                        []
% 11.72/2.00  --share_sel_clauses                     true
% 11.72/2.00  --reset_solvers                         false
% 11.72/2.00  --bc_imp_inh                            [conj_cone]
% 11.72/2.00  --conj_cone_tolerance                   3.
% 11.72/2.00  --extra_neg_conj                        none
% 11.72/2.00  --large_theory_mode                     true
% 11.72/2.00  --prolific_symb_bound                   200
% 11.72/2.00  --lt_threshold                          2000
% 11.72/2.00  --clause_weak_htbl                      true
% 11.72/2.00  --gc_record_bc_elim                     false
% 11.72/2.00  
% 11.72/2.00  ------ Preprocessing Options
% 11.72/2.00  
% 11.72/2.00  --preprocessing_flag                    true
% 11.72/2.00  --time_out_prep_mult                    0.1
% 11.72/2.00  --splitting_mode                        input
% 11.72/2.00  --splitting_grd                         true
% 11.72/2.00  --splitting_cvd                         false
% 11.72/2.00  --splitting_cvd_svl                     false
% 11.72/2.00  --splitting_nvd                         32
% 11.72/2.00  --sub_typing                            true
% 11.72/2.00  --prep_gs_sim                           true
% 11.72/2.00  --prep_unflatten                        true
% 11.72/2.00  --prep_res_sim                          true
% 11.72/2.00  --prep_upred                            true
% 11.72/2.00  --prep_sem_filter                       exhaustive
% 11.72/2.00  --prep_sem_filter_out                   false
% 11.72/2.00  --pred_elim                             true
% 11.72/2.00  --res_sim_input                         true
% 11.72/2.00  --eq_ax_congr_red                       true
% 11.72/2.00  --pure_diseq_elim                       true
% 11.72/2.00  --brand_transform                       false
% 11.72/2.00  --non_eq_to_eq                          false
% 11.72/2.00  --prep_def_merge                        true
% 11.72/2.00  --prep_def_merge_prop_impl              false
% 11.72/2.00  --prep_def_merge_mbd                    true
% 11.72/2.00  --prep_def_merge_tr_red                 false
% 11.72/2.00  --prep_def_merge_tr_cl                  false
% 11.72/2.00  --smt_preprocessing                     true
% 11.72/2.00  --smt_ac_axioms                         fast
% 11.72/2.00  --preprocessed_out                      false
% 11.72/2.00  --preprocessed_stats                    false
% 11.72/2.00  
% 11.72/2.00  ------ Abstraction refinement Options
% 11.72/2.00  
% 11.72/2.00  --abstr_ref                             []
% 11.72/2.00  --abstr_ref_prep                        false
% 11.72/2.00  --abstr_ref_until_sat                   false
% 11.72/2.00  --abstr_ref_sig_restrict                funpre
% 11.72/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.72/2.00  --abstr_ref_under                       []
% 11.72/2.00  
% 11.72/2.00  ------ SAT Options
% 11.72/2.00  
% 11.72/2.00  --sat_mode                              false
% 11.72/2.00  --sat_fm_restart_options                ""
% 11.72/2.00  --sat_gr_def                            false
% 11.72/2.00  --sat_epr_types                         true
% 11.72/2.00  --sat_non_cyclic_types                  false
% 11.72/2.00  --sat_finite_models                     false
% 11.72/2.00  --sat_fm_lemmas                         false
% 11.72/2.00  --sat_fm_prep                           false
% 11.72/2.00  --sat_fm_uc_incr                        true
% 11.72/2.00  --sat_out_model                         small
% 11.72/2.00  --sat_out_clauses                       false
% 11.72/2.00  
% 11.72/2.00  ------ QBF Options
% 11.72/2.00  
% 11.72/2.00  --qbf_mode                              false
% 11.72/2.00  --qbf_elim_univ                         false
% 11.72/2.00  --qbf_dom_inst                          none
% 11.72/2.00  --qbf_dom_pre_inst                      false
% 11.72/2.00  --qbf_sk_in                             false
% 11.72/2.00  --qbf_pred_elim                         true
% 11.72/2.00  --qbf_split                             512
% 11.72/2.00  
% 11.72/2.00  ------ BMC1 Options
% 11.72/2.00  
% 11.72/2.00  --bmc1_incremental                      false
% 11.72/2.00  --bmc1_axioms                           reachable_all
% 11.72/2.00  --bmc1_min_bound                        0
% 11.72/2.00  --bmc1_max_bound                        -1
% 11.72/2.00  --bmc1_max_bound_default                -1
% 11.72/2.00  --bmc1_symbol_reachability              true
% 11.72/2.00  --bmc1_property_lemmas                  false
% 11.72/2.00  --bmc1_k_induction                      false
% 11.72/2.00  --bmc1_non_equiv_states                 false
% 11.72/2.00  --bmc1_deadlock                         false
% 11.72/2.00  --bmc1_ucm                              false
% 11.72/2.00  --bmc1_add_unsat_core                   none
% 11.72/2.00  --bmc1_unsat_core_children              false
% 11.72/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.72/2.00  --bmc1_out_stat                         full
% 11.72/2.00  --bmc1_ground_init                      false
% 11.72/2.00  --bmc1_pre_inst_next_state              false
% 11.72/2.00  --bmc1_pre_inst_state                   false
% 11.72/2.00  --bmc1_pre_inst_reach_state             false
% 11.72/2.00  --bmc1_out_unsat_core                   false
% 11.72/2.00  --bmc1_aig_witness_out                  false
% 11.72/2.00  --bmc1_verbose                          false
% 11.72/2.00  --bmc1_dump_clauses_tptp                false
% 11.72/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.72/2.00  --bmc1_dump_file                        -
% 11.72/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.72/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.72/2.00  --bmc1_ucm_extend_mode                  1
% 11.72/2.00  --bmc1_ucm_init_mode                    2
% 11.72/2.00  --bmc1_ucm_cone_mode                    none
% 11.72/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.72/2.00  --bmc1_ucm_relax_model                  4
% 11.72/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.72/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.72/2.00  --bmc1_ucm_layered_model                none
% 11.72/2.00  --bmc1_ucm_max_lemma_size               10
% 11.72/2.00  
% 11.72/2.00  ------ AIG Options
% 11.72/2.00  
% 11.72/2.00  --aig_mode                              false
% 11.72/2.00  
% 11.72/2.00  ------ Instantiation Options
% 11.72/2.00  
% 11.72/2.00  --instantiation_flag                    true
% 11.72/2.00  --inst_sos_flag                         true
% 11.72/2.00  --inst_sos_phase                        true
% 11.72/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.72/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.72/2.00  --inst_lit_sel_side                     num_symb
% 11.72/2.00  --inst_solver_per_active                1400
% 11.72/2.00  --inst_solver_calls_frac                1.
% 11.72/2.00  --inst_passive_queue_type               priority_queues
% 11.72/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.72/2.00  --inst_passive_queues_freq              [25;2]
% 11.72/2.00  --inst_dismatching                      true
% 11.72/2.00  --inst_eager_unprocessed_to_passive     true
% 11.72/2.00  --inst_prop_sim_given                   true
% 11.72/2.00  --inst_prop_sim_new                     false
% 11.72/2.00  --inst_subs_new                         false
% 11.72/2.00  --inst_eq_res_simp                      false
% 11.72/2.00  --inst_subs_given                       false
% 11.72/2.00  --inst_orphan_elimination               true
% 11.72/2.00  --inst_learning_loop_flag               true
% 11.72/2.00  --inst_learning_start                   3000
% 11.72/2.00  --inst_learning_factor                  2
% 11.72/2.00  --inst_start_prop_sim_after_learn       3
% 11.72/2.00  --inst_sel_renew                        solver
% 11.72/2.00  --inst_lit_activity_flag                true
% 11.72/2.00  --inst_restr_to_given                   false
% 11.72/2.00  --inst_activity_threshold               500
% 11.72/2.00  --inst_out_proof                        true
% 11.72/2.00  
% 11.72/2.00  ------ Resolution Options
% 11.72/2.00  
% 11.72/2.00  --resolution_flag                       true
% 11.72/2.00  --res_lit_sel                           adaptive
% 11.72/2.00  --res_lit_sel_side                      none
% 11.72/2.00  --res_ordering                          kbo
% 11.72/2.00  --res_to_prop_solver                    active
% 11.72/2.00  --res_prop_simpl_new                    false
% 11.72/2.00  --res_prop_simpl_given                  true
% 11.72/2.00  --res_passive_queue_type                priority_queues
% 11.72/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.72/2.00  --res_passive_queues_freq               [15;5]
% 11.72/2.00  --res_forward_subs                      full
% 11.72/2.00  --res_backward_subs                     full
% 11.72/2.00  --res_forward_subs_resolution           true
% 11.72/2.00  --res_backward_subs_resolution          true
% 11.72/2.00  --res_orphan_elimination                true
% 11.72/2.00  --res_time_limit                        2.
% 11.72/2.00  --res_out_proof                         true
% 11.72/2.00  
% 11.72/2.00  ------ Superposition Options
% 11.72/2.00  
% 11.72/2.00  --superposition_flag                    true
% 11.72/2.00  --sup_passive_queue_type                priority_queues
% 11.72/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.72/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.72/2.00  --demod_completeness_check              fast
% 11.72/2.00  --demod_use_ground                      true
% 11.72/2.00  --sup_to_prop_solver                    passive
% 11.72/2.00  --sup_prop_simpl_new                    true
% 11.72/2.00  --sup_prop_simpl_given                  true
% 11.72/2.00  --sup_fun_splitting                     true
% 11.72/2.00  --sup_smt_interval                      50000
% 11.72/2.00  
% 11.72/2.00  ------ Superposition Simplification Setup
% 11.72/2.00  
% 11.72/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.72/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.72/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.72/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.72/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.72/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.72/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.72/2.00  --sup_immed_triv                        [TrivRules]
% 11.72/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.72/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.72/2.00  --sup_immed_bw_main                     []
% 11.72/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.72/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.72/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.72/2.00  --sup_input_bw                          []
% 11.72/2.00  
% 11.72/2.00  ------ Combination Options
% 11.72/2.00  
% 11.72/2.00  --comb_res_mult                         3
% 11.72/2.00  --comb_sup_mult                         2
% 11.72/2.00  --comb_inst_mult                        10
% 11.72/2.00  
% 11.72/2.00  ------ Debug Options
% 11.72/2.00  
% 11.72/2.00  --dbg_backtrace                         false
% 11.72/2.00  --dbg_dump_prop_clauses                 false
% 11.72/2.00  --dbg_dump_prop_clauses_file            -
% 11.72/2.00  --dbg_out_stat                          false
% 11.72/2.00  ------ Parsing...
% 11.72/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.72/2.00  
% 11.72/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.72/2.00  
% 11.72/2.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.72/2.00  
% 11.72/2.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.72/2.00  ------ Proving...
% 11.72/2.00  ------ Problem Properties 
% 11.72/2.00  
% 11.72/2.00  
% 11.72/2.00  clauses                                 49
% 11.72/2.00  conjectures                             8
% 11.72/2.00  EPR                                     13
% 11.72/2.00  Horn                                    24
% 11.72/2.00  unary                                   8
% 11.72/2.00  binary                                  3
% 11.72/2.00  lits                                    247
% 11.72/2.00  lits eq                                 16
% 11.72/2.00  fd_pure                                 0
% 11.72/2.00  fd_pseudo                               0
% 11.72/2.00  fd_cond                                 0
% 11.72/2.00  fd_pseudo_cond                          7
% 11.72/2.00  AC symbols                              0
% 11.72/2.00  
% 11.72/2.00  ------ Schedule dynamic 5 is on 
% 11.72/2.00  
% 11.72/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.72/2.00  
% 11.72/2.00  
% 11.72/2.00  ------ 
% 11.72/2.00  Current options:
% 11.72/2.00  ------ 
% 11.72/2.00  
% 11.72/2.00  ------ Input Options
% 11.72/2.00  
% 11.72/2.00  --out_options                           all
% 11.72/2.00  --tptp_safe_out                         true
% 11.72/2.00  --problem_path                          ""
% 11.72/2.00  --include_path                          ""
% 11.72/2.00  --clausifier                            res/vclausify_rel
% 11.72/2.00  --clausifier_options                    ""
% 11.72/2.00  --stdin                                 false
% 11.72/2.00  --stats_out                             all
% 11.72/2.00  
% 11.72/2.00  ------ General Options
% 11.72/2.00  
% 11.72/2.00  --fof                                   false
% 11.72/2.00  --time_out_real                         305.
% 11.72/2.00  --time_out_virtual                      -1.
% 11.72/2.00  --symbol_type_check                     false
% 11.72/2.00  --clausify_out                          false
% 11.72/2.00  --sig_cnt_out                           false
% 11.72/2.00  --trig_cnt_out                          false
% 11.72/2.00  --trig_cnt_out_tolerance                1.
% 11.72/2.00  --trig_cnt_out_sk_spl                   false
% 11.72/2.00  --abstr_cl_out                          false
% 11.72/2.00  
% 11.72/2.00  ------ Global Options
% 11.72/2.00  
% 11.72/2.00  --schedule                              default
% 11.72/2.00  --add_important_lit                     false
% 11.72/2.00  --prop_solver_per_cl                    1000
% 11.72/2.00  --min_unsat_core                        false
% 11.72/2.00  --soft_assumptions                      false
% 11.72/2.00  --soft_lemma_size                       3
% 11.72/2.00  --prop_impl_unit_size                   0
% 11.72/2.00  --prop_impl_unit                        []
% 11.72/2.00  --share_sel_clauses                     true
% 11.72/2.00  --reset_solvers                         false
% 11.72/2.00  --bc_imp_inh                            [conj_cone]
% 11.72/2.00  --conj_cone_tolerance                   3.
% 11.72/2.00  --extra_neg_conj                        none
% 11.72/2.00  --large_theory_mode                     true
% 11.72/2.00  --prolific_symb_bound                   200
% 11.72/2.00  --lt_threshold                          2000
% 11.72/2.00  --clause_weak_htbl                      true
% 11.72/2.00  --gc_record_bc_elim                     false
% 11.72/2.00  
% 11.72/2.00  ------ Preprocessing Options
% 11.72/2.00  
% 11.72/2.00  --preprocessing_flag                    true
% 11.72/2.00  --time_out_prep_mult                    0.1
% 11.72/2.00  --splitting_mode                        input
% 11.72/2.00  --splitting_grd                         true
% 11.72/2.00  --splitting_cvd                         false
% 11.72/2.00  --splitting_cvd_svl                     false
% 11.72/2.00  --splitting_nvd                         32
% 11.72/2.00  --sub_typing                            true
% 11.72/2.00  --prep_gs_sim                           true
% 11.72/2.00  --prep_unflatten                        true
% 11.72/2.00  --prep_res_sim                          true
% 11.72/2.00  --prep_upred                            true
% 11.72/2.00  --prep_sem_filter                       exhaustive
% 11.72/2.00  --prep_sem_filter_out                   false
% 11.72/2.00  --pred_elim                             true
% 11.72/2.00  --res_sim_input                         true
% 11.72/2.00  --eq_ax_congr_red                       true
% 11.72/2.00  --pure_diseq_elim                       true
% 11.72/2.00  --brand_transform                       false
% 11.72/2.00  --non_eq_to_eq                          false
% 11.72/2.00  --prep_def_merge                        true
% 11.72/2.00  --prep_def_merge_prop_impl              false
% 11.72/2.00  --prep_def_merge_mbd                    true
% 11.72/2.00  --prep_def_merge_tr_red                 false
% 11.72/2.00  --prep_def_merge_tr_cl                  false
% 11.72/2.00  --smt_preprocessing                     true
% 11.72/2.00  --smt_ac_axioms                         fast
% 11.72/2.00  --preprocessed_out                      false
% 11.72/2.00  --preprocessed_stats                    false
% 11.72/2.00  
% 11.72/2.00  ------ Abstraction refinement Options
% 11.72/2.00  
% 11.72/2.00  --abstr_ref                             []
% 11.72/2.00  --abstr_ref_prep                        false
% 11.72/2.00  --abstr_ref_until_sat                   false
% 11.72/2.00  --abstr_ref_sig_restrict                funpre
% 11.72/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.72/2.00  --abstr_ref_under                       []
% 11.72/2.00  
% 11.72/2.00  ------ SAT Options
% 11.72/2.00  
% 11.72/2.00  --sat_mode                              false
% 11.72/2.00  --sat_fm_restart_options                ""
% 11.72/2.00  --sat_gr_def                            false
% 11.72/2.00  --sat_epr_types                         true
% 11.72/2.00  --sat_non_cyclic_types                  false
% 11.72/2.00  --sat_finite_models                     false
% 11.72/2.00  --sat_fm_lemmas                         false
% 11.72/2.00  --sat_fm_prep                           false
% 11.72/2.00  --sat_fm_uc_incr                        true
% 11.72/2.00  --sat_out_model                         small
% 11.72/2.00  --sat_out_clauses                       false
% 11.72/2.00  
% 11.72/2.00  ------ QBF Options
% 11.72/2.00  
% 11.72/2.00  --qbf_mode                              false
% 11.72/2.00  --qbf_elim_univ                         false
% 11.72/2.00  --qbf_dom_inst                          none
% 11.72/2.00  --qbf_dom_pre_inst                      false
% 11.72/2.00  --qbf_sk_in                             false
% 11.72/2.00  --qbf_pred_elim                         true
% 11.72/2.00  --qbf_split                             512
% 11.72/2.00  
% 11.72/2.00  ------ BMC1 Options
% 11.72/2.00  
% 11.72/2.00  --bmc1_incremental                      false
% 11.72/2.00  --bmc1_axioms                           reachable_all
% 11.72/2.00  --bmc1_min_bound                        0
% 11.72/2.00  --bmc1_max_bound                        -1
% 11.72/2.00  --bmc1_max_bound_default                -1
% 11.72/2.00  --bmc1_symbol_reachability              true
% 11.72/2.00  --bmc1_property_lemmas                  false
% 11.72/2.00  --bmc1_k_induction                      false
% 11.72/2.00  --bmc1_non_equiv_states                 false
% 11.72/2.00  --bmc1_deadlock                         false
% 11.72/2.00  --bmc1_ucm                              false
% 11.72/2.00  --bmc1_add_unsat_core                   none
% 11.72/2.00  --bmc1_unsat_core_children              false
% 11.72/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.72/2.00  --bmc1_out_stat                         full
% 11.72/2.00  --bmc1_ground_init                      false
% 11.72/2.00  --bmc1_pre_inst_next_state              false
% 11.72/2.00  --bmc1_pre_inst_state                   false
% 11.72/2.00  --bmc1_pre_inst_reach_state             false
% 11.72/2.00  --bmc1_out_unsat_core                   false
% 11.72/2.00  --bmc1_aig_witness_out                  false
% 11.72/2.00  --bmc1_verbose                          false
% 11.72/2.00  --bmc1_dump_clauses_tptp                false
% 11.72/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.72/2.00  --bmc1_dump_file                        -
% 11.72/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.72/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.72/2.00  --bmc1_ucm_extend_mode                  1
% 11.72/2.00  --bmc1_ucm_init_mode                    2
% 11.72/2.00  --bmc1_ucm_cone_mode                    none
% 11.72/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.72/2.00  --bmc1_ucm_relax_model                  4
% 11.72/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.72/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.72/2.00  --bmc1_ucm_layered_model                none
% 11.72/2.00  --bmc1_ucm_max_lemma_size               10
% 11.72/2.00  
% 11.72/2.00  ------ AIG Options
% 11.72/2.00  
% 11.72/2.00  --aig_mode                              false
% 11.72/2.00  
% 11.72/2.00  ------ Instantiation Options
% 11.72/2.00  
% 11.72/2.00  --instantiation_flag                    true
% 11.72/2.00  --inst_sos_flag                         true
% 11.72/2.00  --inst_sos_phase                        true
% 11.72/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.72/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.72/2.00  --inst_lit_sel_side                     none
% 11.72/2.00  --inst_solver_per_active                1400
% 11.72/2.00  --inst_solver_calls_frac                1.
% 11.72/2.00  --inst_passive_queue_type               priority_queues
% 11.72/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.72/2.00  --inst_passive_queues_freq              [25;2]
% 11.72/2.00  --inst_dismatching                      true
% 11.72/2.00  --inst_eager_unprocessed_to_passive     true
% 11.72/2.00  --inst_prop_sim_given                   true
% 11.72/2.00  --inst_prop_sim_new                     false
% 11.72/2.00  --inst_subs_new                         false
% 11.72/2.00  --inst_eq_res_simp                      false
% 11.72/2.00  --inst_subs_given                       false
% 11.72/2.00  --inst_orphan_elimination               true
% 11.72/2.00  --inst_learning_loop_flag               true
% 11.72/2.00  --inst_learning_start                   3000
% 11.72/2.00  --inst_learning_factor                  2
% 11.72/2.00  --inst_start_prop_sim_after_learn       3
% 11.72/2.00  --inst_sel_renew                        solver
% 11.72/2.00  --inst_lit_activity_flag                true
% 11.72/2.00  --inst_restr_to_given                   false
% 11.72/2.00  --inst_activity_threshold               500
% 11.72/2.00  --inst_out_proof                        true
% 11.72/2.00  
% 11.72/2.00  ------ Resolution Options
% 11.72/2.00  
% 11.72/2.00  --resolution_flag                       false
% 11.72/2.00  --res_lit_sel                           adaptive
% 11.72/2.00  --res_lit_sel_side                      none
% 11.72/2.00  --res_ordering                          kbo
% 11.72/2.00  --res_to_prop_solver                    active
% 11.72/2.00  --res_prop_simpl_new                    false
% 11.72/2.00  --res_prop_simpl_given                  true
% 11.72/2.00  --res_passive_queue_type                priority_queues
% 11.72/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.72/2.00  --res_passive_queues_freq               [15;5]
% 11.72/2.00  --res_forward_subs                      full
% 11.72/2.00  --res_backward_subs                     full
% 11.72/2.00  --res_forward_subs_resolution           true
% 11.72/2.00  --res_backward_subs_resolution          true
% 11.72/2.00  --res_orphan_elimination                true
% 11.72/2.00  --res_time_limit                        2.
% 11.72/2.00  --res_out_proof                         true
% 11.72/2.00  
% 11.72/2.00  ------ Superposition Options
% 11.72/2.00  
% 11.72/2.00  --superposition_flag                    true
% 11.72/2.00  --sup_passive_queue_type                priority_queues
% 11.72/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.72/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.72/2.00  --demod_completeness_check              fast
% 11.72/2.00  --demod_use_ground                      true
% 11.72/2.00  --sup_to_prop_solver                    passive
% 11.72/2.00  --sup_prop_simpl_new                    true
% 11.72/2.00  --sup_prop_simpl_given                  true
% 11.72/2.00  --sup_fun_splitting                     true
% 11.72/2.00  --sup_smt_interval                      50000
% 11.72/2.00  
% 11.72/2.00  ------ Superposition Simplification Setup
% 11.72/2.00  
% 11.72/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.72/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.72/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.72/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.72/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.72/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.72/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.72/2.00  --sup_immed_triv                        [TrivRules]
% 11.72/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.72/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.72/2.00  --sup_immed_bw_main                     []
% 11.72/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.72/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.72/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.72/2.00  --sup_input_bw                          []
% 11.72/2.00  
% 11.72/2.00  ------ Combination Options
% 11.72/2.00  
% 11.72/2.00  --comb_res_mult                         3
% 11.72/2.00  --comb_sup_mult                         2
% 11.72/2.00  --comb_inst_mult                        10
% 11.72/2.00  
% 11.72/2.00  ------ Debug Options
% 11.72/2.00  
% 11.72/2.00  --dbg_backtrace                         false
% 11.72/2.00  --dbg_dump_prop_clauses                 false
% 11.72/2.00  --dbg_dump_prop_clauses_file            -
% 11.72/2.00  --dbg_out_stat                          false
% 11.72/2.00  
% 11.72/2.00  
% 11.72/2.00  
% 11.72/2.00  
% 11.72/2.00  ------ Proving...
% 11.72/2.00  
% 11.72/2.00  
% 11.72/2.00  % SZS status Theorem for theBenchmark.p
% 11.72/2.00  
% 11.72/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.72/2.00  
% 11.72/2.00  fof(f21,conjecture,(
% 11.72/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)))))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f22,negated_conjecture,(
% 11.72/2.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2)))))))),
% 11.72/2.00    inference(negated_conjecture,[],[f21])).
% 11.72/2.00  
% 11.72/2.00  fof(f57,plain,(
% 11.72/2.00    ? [X0] : (? [X1] : (? [X2] : (((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f22])).
% 11.72/2.00  
% 11.72/2.00  fof(f58,plain,(
% 11.72/2.00    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f57])).
% 11.72/2.00  
% 11.72/2.00  fof(f73,plain,(
% 11.72/2.00    ( ! [X0,X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5),sK5,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK5))) & r1_tsep_1(X1,sK5) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 11.72/2.00    introduced(choice_axiom,[])).
% 11.72/2.00  
% 11.72/2.00  fof(f72,plain,(
% 11.72/2.00    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,sK4))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2),X2,k8_tmap_1(X0,sK4)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,sK4))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,sK4),k9_tmap_1(X0,sK4),X2))) & r1_tsep_1(sK4,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 11.72/2.00    introduced(choice_axiom,[])).
% 11.72/2.00  
% 11.72/2.00  fof(f71,plain,(
% 11.72/2.00    ? [X0] : (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X2,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK3,X1))))) | ~v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2),X2,k8_tmap_1(sK3,X1)) | ~v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(sK3,X1))) | ~v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,X1),k9_tmap_1(sK3,X1),X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 11.72/2.00    introduced(choice_axiom,[])).
% 11.72/2.00  
% 11.72/2.00  fof(f74,plain,(
% 11.72/2.00    (((~m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))) & r1_tsep_1(sK4,sK5) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 11.72/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f58,f73,f72,f71])).
% 11.72/2.00  
% 11.72/2.00  fof(f121,plain,(
% 11.72/2.00    m1_pre_topc(sK4,sK3)),
% 11.72/2.00    inference(cnf_transformation,[],[f74])).
% 11.72/2.00  
% 11.72/2.00  fof(f7,axiom,(
% 11.72/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f32,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f7])).
% 11.72/2.00  
% 11.72/2.00  fof(f33,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f32])).
% 11.72/2.00  
% 11.72/2.00  fof(f62,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(nnf_transformation,[],[f33])).
% 11.72/2.00  
% 11.72/2.00  fof(f63,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(rectify,[],[f62])).
% 11.72/2.00  
% 11.72/2.00  fof(f64,plain,(
% 11.72/2.00    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.72/2.00    introduced(choice_axiom,[])).
% 11.72/2.00  
% 11.72/2.00  fof(f65,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f64])).
% 11.72/2.00  
% 11.72/2.00  fof(f82,plain,(
% 11.72/2.00    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f65])).
% 11.72/2.00  
% 11.72/2.00  fof(f127,plain,(
% 11.72/2.00    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(equality_resolution,[],[f82])).
% 11.72/2.00  
% 11.72/2.00  fof(f128,plain,(
% 11.72/2.00    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(equality_resolution,[],[f127])).
% 11.72/2.00  
% 11.72/2.00  fof(f18,axiom,(
% 11.72/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f53,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.72/2.00    inference(ennf_transformation,[],[f18])).
% 11.72/2.00  
% 11.72/2.00  fof(f114,plain,(
% 11.72/2.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f53])).
% 11.72/2.00  
% 11.72/2.00  fof(f14,axiom,(
% 11.72/2.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f45,plain,(
% 11.72/2.00    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f14])).
% 11.72/2.00  
% 11.72/2.00  fof(f46,plain,(
% 11.72/2.00    ! [X0,X1] : ((v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1)) & ~v2_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f45])).
% 11.72/2.00  
% 11.72/2.00  fof(f105,plain,(
% 11.72/2.00    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f46])).
% 11.72/2.00  
% 11.72/2.00  fof(f106,plain,(
% 11.72/2.00    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f46])).
% 11.72/2.00  
% 11.72/2.00  fof(f12,axiom,(
% 11.72/2.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f41,plain,(
% 11.72/2.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f12])).
% 11.72/2.00  
% 11.72/2.00  fof(f42,plain,(
% 11.72/2.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f41])).
% 11.72/2.00  
% 11.72/2.00  fof(f100,plain,(
% 11.72/2.00    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f42])).
% 11.72/2.00  
% 11.72/2.00  fof(f117,plain,(
% 11.72/2.00    ~v2_struct_0(sK3)),
% 11.72/2.00    inference(cnf_transformation,[],[f74])).
% 11.72/2.00  
% 11.72/2.00  fof(f118,plain,(
% 11.72/2.00    v2_pre_topc(sK3)),
% 11.72/2.00    inference(cnf_transformation,[],[f74])).
% 11.72/2.00  
% 11.72/2.00  fof(f119,plain,(
% 11.72/2.00    l1_pre_topc(sK3)),
% 11.72/2.00    inference(cnf_transformation,[],[f74])).
% 11.72/2.00  
% 11.72/2.00  fof(f11,axiom,(
% 11.72/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f39,plain,(
% 11.72/2.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f11])).
% 11.72/2.00  
% 11.72/2.00  fof(f40,plain,(
% 11.72/2.00    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f39])).
% 11.72/2.00  
% 11.72/2.00  fof(f97,plain,(
% 11.72/2.00    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f40])).
% 11.72/2.00  
% 11.72/2.00  fof(f10,axiom,(
% 11.72/2.00    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f37,plain,(
% 11.72/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f10])).
% 11.72/2.00  
% 11.72/2.00  fof(f38,plain,(
% 11.72/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f37])).
% 11.72/2.00  
% 11.72/2.00  fof(f92,plain,(
% 11.72/2.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f38])).
% 11.72/2.00  
% 11.72/2.00  fof(f123,plain,(
% 11.72/2.00    m1_pre_topc(sK5,sK3)),
% 11.72/2.00    inference(cnf_transformation,[],[f74])).
% 11.72/2.00  
% 11.72/2.00  fof(f4,axiom,(
% 11.72/2.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f26,plain,(
% 11.72/2.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f4])).
% 11.72/2.00  
% 11.72/2.00  fof(f27,plain,(
% 11.72/2.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f26])).
% 11.72/2.00  
% 11.72/2.00  fof(f78,plain,(
% 11.72/2.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f27])).
% 11.72/2.00  
% 11.72/2.00  fof(f1,axiom,(
% 11.72/2.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f23,plain,(
% 11.72/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.72/2.00    inference(ennf_transformation,[],[f1])).
% 11.72/2.00  
% 11.72/2.00  fof(f75,plain,(
% 11.72/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f23])).
% 11.72/2.00  
% 11.72/2.00  fof(f2,axiom,(
% 11.72/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f24,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.72/2.00    inference(ennf_transformation,[],[f2])).
% 11.72/2.00  
% 11.72/2.00  fof(f76,plain,(
% 11.72/2.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f24])).
% 11.72/2.00  
% 11.72/2.00  fof(f124,plain,(
% 11.72/2.00    r1_tsep_1(sK4,sK5)),
% 11.72/2.00    inference(cnf_transformation,[],[f74])).
% 11.72/2.00  
% 11.72/2.00  fof(f15,axiom,(
% 11.72/2.00    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f47,plain,(
% 11.72/2.00    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f15])).
% 11.72/2.00  
% 11.72/2.00  fof(f48,plain,(
% 11.72/2.00    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f47])).
% 11.72/2.00  
% 11.72/2.00  fof(f107,plain,(
% 11.72/2.00    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f48])).
% 11.72/2.00  
% 11.72/2.00  fof(f13,axiom,(
% 11.72/2.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f43,plain,(
% 11.72/2.00    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f13])).
% 11.72/2.00  
% 11.72/2.00  fof(f44,plain,(
% 11.72/2.00    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f43])).
% 11.72/2.00  
% 11.72/2.00  fof(f101,plain,(
% 11.72/2.00    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f44])).
% 11.72/2.00  
% 11.72/2.00  fof(f9,axiom,(
% 11.72/2.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f36,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 11.72/2.00    inference(ennf_transformation,[],[f9])).
% 11.72/2.00  
% 11.72/2.00  fof(f70,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 11.72/2.00    inference(nnf_transformation,[],[f36])).
% 11.72/2.00  
% 11.72/2.00  fof(f90,plain,(
% 11.72/2.00    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f70])).
% 11.72/2.00  
% 11.72/2.00  fof(f102,plain,(
% 11.72/2.00    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f44])).
% 11.72/2.00  
% 11.72/2.00  fof(f103,plain,(
% 11.72/2.00    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f44])).
% 11.72/2.00  
% 11.72/2.00  fof(f93,plain,(
% 11.72/2.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f38])).
% 11.72/2.00  
% 11.72/2.00  fof(f94,plain,(
% 11.72/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f38])).
% 11.72/2.00  
% 11.72/2.00  fof(f17,axiom,(
% 11.72/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f51,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : (((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f17])).
% 11.72/2.00  
% 11.72/2.00  fof(f52,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : ((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f51])).
% 11.72/2.00  
% 11.72/2.00  fof(f112,plain,(
% 11.72/2.00    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f52])).
% 11.72/2.00  
% 11.72/2.00  fof(f125,plain,(
% 11.72/2.00    ~m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))))) | ~v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4)) | ~v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) | ~v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))),
% 11.72/2.00    inference(cnf_transformation,[],[f74])).
% 11.72/2.00  
% 11.72/2.00  fof(f122,plain,(
% 11.72/2.00    ~v2_struct_0(sK5)),
% 11.72/2.00    inference(cnf_transformation,[],[f74])).
% 11.72/2.00  
% 11.72/2.00  fof(f96,plain,(
% 11.72/2.00    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f40])).
% 11.72/2.00  
% 11.72/2.00  fof(f8,axiom,(
% 11.72/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f34,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f8])).
% 11.72/2.00  
% 11.72/2.00  fof(f35,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f34])).
% 11.72/2.00  
% 11.72/2.00  fof(f66,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(nnf_transformation,[],[f35])).
% 11.72/2.00  
% 11.72/2.00  fof(f67,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(rectify,[],[f66])).
% 11.72/2.00  
% 11.72/2.00  fof(f68,plain,(
% 11.72/2.00    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.72/2.00    introduced(choice_axiom,[])).
% 11.72/2.00  
% 11.72/2.00  fof(f69,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK2(X0,X1,X2))),X2,k7_tmap_1(X0,sK2(X0,X1,X2))) & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f67,f68])).
% 11.72/2.00  
% 11.72/2.00  fof(f86,plain,(
% 11.72/2.00    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f69])).
% 11.72/2.00  
% 11.72/2.00  fof(f129,plain,(
% 11.72/2.00    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(equality_resolution,[],[f86])).
% 11.72/2.00  
% 11.72/2.00  fof(f130,plain,(
% 11.72/2.00    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(equality_resolution,[],[f129])).
% 11.72/2.00  
% 11.72/2.00  fof(f5,axiom,(
% 11.72/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f28,plain,(
% 11.72/2.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 11.72/2.00    inference(ennf_transformation,[],[f5])).
% 11.72/2.00  
% 11.72/2.00  fof(f29,plain,(
% 11.72/2.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 11.72/2.00    inference(flattening,[],[f28])).
% 11.72/2.00  
% 11.72/2.00  fof(f61,plain,(
% 11.72/2.00    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 11.72/2.00    inference(nnf_transformation,[],[f29])).
% 11.72/2.00  
% 11.72/2.00  fof(f79,plain,(
% 11.72/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f61])).
% 11.72/2.00  
% 11.72/2.00  fof(f16,axiom,(
% 11.72/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f49,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f16])).
% 11.72/2.00  
% 11.72/2.00  fof(f50,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f49])).
% 11.72/2.00  
% 11.72/2.00  fof(f108,plain,(
% 11.72/2.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f50])).
% 11.72/2.00  
% 11.72/2.00  fof(f6,axiom,(
% 11.72/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f30,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.72/2.00    inference(ennf_transformation,[],[f6])).
% 11.72/2.00  
% 11.72/2.00  fof(f31,plain,(
% 11.72/2.00    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.72/2.00    inference(flattening,[],[f30])).
% 11.72/2.00  
% 11.72/2.00  fof(f81,plain,(
% 11.72/2.00    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f31])).
% 11.72/2.00  
% 11.72/2.00  fof(f19,axiom,(
% 11.72/2.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 11.72/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.72/2.00  
% 11.72/2.00  fof(f54,plain,(
% 11.72/2.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 11.72/2.00    inference(ennf_transformation,[],[f19])).
% 11.72/2.00  
% 11.72/2.00  fof(f115,plain,(
% 11.72/2.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f54])).
% 11.72/2.00  
% 11.72/2.00  fof(f95,plain,(
% 11.72/2.00    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.72/2.00    inference(cnf_transformation,[],[f40])).
% 11.72/2.00  
% 11.72/2.00  cnf(c_46,negated_conjecture,
% 11.72/2.00      ( m1_pre_topc(sK4,sK3) ),
% 11.72/2.00      inference(cnf_transformation,[],[f121]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1869,negated_conjecture,
% 11.72/2.00      ( m1_pre_topc(sK4,sK3) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_46]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2841,plain,
% 11.72/2.00      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1869]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_10,plain,
% 11.72/2.00      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/2.00      | ~ m1_pre_topc(X0,X1)
% 11.72/2.00      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1)
% 11.72/2.00      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 11.72/2.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 11.72/2.00      inference(cnf_transformation,[],[f128]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_39,plain,
% 11.72/2.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/2.00      | ~ m1_pre_topc(X0,X1)
% 11.72/2.00      | ~ l1_pre_topc(X1) ),
% 11.72/2.00      inference(cnf_transformation,[],[f114]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_30,plain,
% 11.72/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.72/2.00      | v1_pre_topc(k8_tmap_1(X1,X0))
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1) ),
% 11.72/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_29,plain,
% 11.72/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | v2_pre_topc(k8_tmap_1(X1,X0))
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1) ),
% 11.72/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_23,plain,
% 11.72/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1)
% 11.72/2.00      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 11.72/2.00      inference(cnf_transformation,[],[f100]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_325,plain,
% 11.72/2.00      ( ~ l1_pre_topc(X1)
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ m1_pre_topc(X0,X1)
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_10,c_39,c_30,c_29,c_23]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_326,plain,
% 11.72/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1)
% 11.72/2.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 11.72/2.00      inference(renaming,[status(thm)],[c_325]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1863,plain,
% 11.72/2.00      ( ~ m1_pre_topc(X0_60,X1_60)
% 11.72/2.00      | ~ v2_pre_topc(X1_60)
% 11.72/2.00      | v2_struct_0(X1_60)
% 11.72/2.00      | ~ l1_pre_topc(X1_60)
% 11.72/2.00      | k6_tmap_1(X1_60,u1_struct_0(X0_60)) = k8_tmap_1(X1_60,X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_326]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2847,plain,
% 11.72/2.00      ( k6_tmap_1(X0_60,u1_struct_0(X1_60)) = k8_tmap_1(X0_60,X1_60)
% 11.72/2.00      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1863]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_8621,plain,
% 11.72/2.00      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4)
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2841,c_2847]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_50,negated_conjecture,
% 11.72/2.00      ( ~ v2_struct_0(sK3) ),
% 11.72/2.00      inference(cnf_transformation,[],[f117]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_51,plain,
% 11.72/2.00      ( v2_struct_0(sK3) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_49,negated_conjecture,
% 11.72/2.00      ( v2_pre_topc(sK3) ),
% 11.72/2.00      inference(cnf_transformation,[],[f118]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_52,plain,
% 11.72/2.00      ( v2_pre_topc(sK3) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_48,negated_conjecture,
% 11.72/2.00      ( l1_pre_topc(sK3) ),
% 11.72/2.00      inference(cnf_transformation,[],[f119]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_53,plain,
% 11.72/2.00      ( l1_pre_topc(sK3) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_8848,plain,
% 11.72/2.00      ( k6_tmap_1(sK3,u1_struct_0(sK4)) = k8_tmap_1(sK3,sK4) ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_8621,c_51,c_52,c_53]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_20,plain,
% 11.72/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/2.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1) ),
% 11.72/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1891,plain,
% 11.72/2.00      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
% 11.72/2.00      | m1_subset_1(k7_tmap_1(X0_60,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_59)))))
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_20]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2819,plain,
% 11.72/2.00      ( m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
% 11.72/2.00      | m1_subset_1(k7_tmap_1(X0_60,X0_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_59))))) = iProver_top
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1891]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_8857,plain,
% 11.72/2.00      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
% 11.72/2.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_8848,c_2819]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_55,plain,
% 11.72/2.00      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1875,plain,
% 11.72/2.00      ( m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(X1_60)))
% 11.72/2.00      | ~ m1_pre_topc(X0_60,X1_60)
% 11.72/2.00      | ~ l1_pre_topc(X1_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_39]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_7131,plain,
% 11.72/2.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0_60)))
% 11.72/2.00      | ~ m1_pre_topc(sK4,X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1875]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_7132,plain,
% 11.72/2.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0_60))) = iProver_top
% 11.72/2.00      | m1_pre_topc(sK4,X0_60) != iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_7131]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_7134,plain,
% 11.72/2.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 11.72/2.00      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_7132]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_9046,plain,
% 11.72/2.00      ( m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_8857,c_51,c_52,c_53,c_55,c_7134]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_19,plain,
% 11.72/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.72/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.72/2.00      | ~ v1_funct_1(X0)
% 11.72/2.00      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3))
% 11.72/2.00      | ~ l1_struct_0(X1)
% 11.72/2.00      | ~ l1_struct_0(X2)
% 11.72/2.00      | ~ l1_struct_0(X3) ),
% 11.72/2.00      inference(cnf_transformation,[],[f92]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1892,plain,
% 11.72/2.00      ( ~ v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60))
% 11.72/2.00      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60))))
% 11.72/2.00      | ~ v1_funct_1(X0_59)
% 11.72/2.00      | v1_funct_1(k2_tmap_1(X0_60,X1_60,X0_59,X2_60))
% 11.72/2.00      | ~ l1_struct_0(X0_60)
% 11.72/2.00      | ~ l1_struct_0(X1_60)
% 11.72/2.00      | ~ l1_struct_0(X2_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_19]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2818,plain,
% 11.72/2.00      ( v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60)) != iProver_top
% 11.72/2.00      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60)))) != iProver_top
% 11.72/2.00      | v1_funct_1(X0_59) != iProver_top
% 11.72/2.00      | v1_funct_1(k2_tmap_1(X0_60,X1_60,X0_59,X2_60)) = iProver_top
% 11.72/2.00      | l1_struct_0(X0_60) != iProver_top
% 11.72/2.00      | l1_struct_0(X1_60) != iProver_top
% 11.72/2.00      | l1_struct_0(X2_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1892]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_9050,plain,
% 11.72/2.00      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4)),X0_60)) = iProver_top
% 11.72/2.00      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 11.72/2.00      | l1_struct_0(X0_60) != iProver_top
% 11.72/2.00      | l1_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top
% 11.72/2.00      | l1_struct_0(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_9046,c_2818]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_44,negated_conjecture,
% 11.72/2.00      ( m1_pre_topc(sK5,sK3) ),
% 11.72/2.00      inference(cnf_transformation,[],[f123]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3,plain,
% 11.72/2.00      ( v2_struct_0(X0)
% 11.72/2.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 11.72/2.00      | ~ l1_struct_0(X0) ),
% 11.72/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_166,plain,
% 11.72/2.00      ( v2_struct_0(X0) = iProver_top
% 11.72/2.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 11.72/2.00      | l1_struct_0(X0) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_168,plain,
% 11.72/2.00      ( v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 11.72/2.00      | l1_struct_0(sK3) != iProver_top ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_166]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_0,plain,
% 11.72/2.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 11.72/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_173,plain,
% 11.72/2.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_175,plain,
% 11.72/2.00      ( l1_pre_topc(sK3) != iProver_top
% 11.72/2.00      | l1_struct_0(sK3) = iProver_top ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_173]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1922,plain,
% 11.72/2.00      ( X0_60 != X1_60 | u1_struct_0(X0_60) = u1_struct_0(X1_60) ),
% 11.72/2.00      theory(equality) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1944,plain,
% 11.72/2.00      ( sK3 != sK3 | u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1922]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1914,plain,( X0_60 = X0_60 ),theory(equality) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1966,plain,
% 11.72/2.00      ( sK3 = sK3 ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1914]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1909,plain,
% 11.72/2.00      ( ~ l1_pre_topc(X0_60) | l1_struct_0(X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_0]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3193,plain,
% 11.72/2.00      ( ~ l1_pre_topc(sK4) | l1_struct_0(sK4) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1909]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3196,plain,
% 11.72/2.00      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1909]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1871,negated_conjecture,
% 11.72/2.00      ( m1_pre_topc(sK5,sK3) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_44]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2839,plain,
% 11.72/2.00      ( m1_pre_topc(sK5,sK3) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1871]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1,plain,
% 11.72/2.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.72/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1908,plain,
% 11.72/2.00      ( ~ m1_pre_topc(X0_60,X1_60)
% 11.72/2.00      | ~ l1_pre_topc(X1_60)
% 11.72/2.00      | l1_pre_topc(X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_1]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2802,plain,
% 11.72/2.00      ( m1_pre_topc(X0_60,X1_60) != iProver_top
% 11.72/2.00      | l1_pre_topc(X1_60) != iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1908]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3551,plain,
% 11.72/2.00      ( l1_pre_topc(sK5) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2839,c_2802]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3555,plain,
% 11.72/2.00      ( l1_pre_topc(sK5) | ~ l1_pre_topc(sK3) ),
% 11.72/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_3551]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3552,plain,
% 11.72/2.00      ( l1_pre_topc(sK4) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2841,c_2802]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3556,plain,
% 11.72/2.00      ( l1_pre_topc(sK4) | ~ l1_pre_topc(sK3) ),
% 11.72/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_3552]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_43,negated_conjecture,
% 11.72/2.00      ( r1_tsep_1(sK4,sK5) ),
% 11.72/2.00      inference(cnf_transformation,[],[f124]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1872,negated_conjecture,
% 11.72/2.00      ( r1_tsep_1(sK4,sK5) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_43]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2838,plain,
% 11.72/2.00      ( r1_tsep_1(sK4,sK5) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1872]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_32,plain,
% 11.72/2.00      ( ~ r1_tsep_1(X0,X1)
% 11.72/2.00      | r1_tsep_1(X1,X0)
% 11.72/2.00      | ~ l1_struct_0(X0)
% 11.72/2.00      | ~ l1_struct_0(X1) ),
% 11.72/2.00      inference(cnf_transformation,[],[f107]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1881,plain,
% 11.72/2.00      ( ~ r1_tsep_1(X0_60,X1_60)
% 11.72/2.00      | r1_tsep_1(X1_60,X0_60)
% 11.72/2.00      | ~ l1_struct_0(X0_60)
% 11.72/2.00      | ~ l1_struct_0(X1_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_32]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2829,plain,
% 11.72/2.00      ( r1_tsep_1(X0_60,X1_60) != iProver_top
% 11.72/2.00      | r1_tsep_1(X1_60,X0_60) = iProver_top
% 11.72/2.00      | l1_struct_0(X0_60) != iProver_top
% 11.72/2.00      | l1_struct_0(X1_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1881]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3880,plain,
% 11.72/2.00      ( r1_tsep_1(sK5,sK4) = iProver_top
% 11.72/2.00      | l1_struct_0(sK5) != iProver_top
% 11.72/2.00      | l1_struct_0(sK4) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2838,c_2829]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3881,plain,
% 11.72/2.00      ( r1_tsep_1(sK5,sK4) | ~ l1_struct_0(sK5) | ~ l1_struct_0(sK4) ),
% 11.72/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_3880]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_28,plain,
% 11.72/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | v1_funct_1(k9_tmap_1(X1,X0))
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1) ),
% 11.72/2.00      inference(cnf_transformation,[],[f101]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1883,plain,
% 11.72/2.00      ( ~ m1_pre_topc(X0_60,X1_60)
% 11.72/2.00      | ~ v2_pre_topc(X1_60)
% 11.72/2.00      | v1_funct_1(k9_tmap_1(X1_60,X0_60))
% 11.72/2.00      | v2_struct_0(X1_60)
% 11.72/2.00      | ~ l1_pre_topc(X1_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_28]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3931,plain,
% 11.72/2.00      ( ~ m1_pre_topc(sK4,sK3)
% 11.72/2.00      | ~ v2_pre_topc(sK3)
% 11.72/2.00      | v1_funct_1(k9_tmap_1(sK3,sK4))
% 11.72/2.00      | v2_struct_0(sK3)
% 11.72/2.00      | ~ l1_pre_topc(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1883]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3932,plain,
% 11.72/2.00      ( m1_pre_topc(sK4,sK3) != iProver_top
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v1_funct_1(k9_tmap_1(sK3,sK4)) = iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_3931]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_4557,plain,
% 11.72/2.00      ( sK5 = sK5 ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1914]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_16,plain,
% 11.72/2.00      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 11.72/2.00      | ~ r1_tsep_1(X0,X1)
% 11.72/2.00      | ~ l1_struct_0(X0)
% 11.72/2.00      | ~ l1_struct_0(X1) ),
% 11.72/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1895,plain,
% 11.72/2.00      ( r1_xboole_0(u1_struct_0(X0_60),u1_struct_0(X1_60))
% 11.72/2.00      | ~ r1_tsep_1(X0_60,X1_60)
% 11.72/2.00      | ~ l1_struct_0(X0_60)
% 11.72/2.00      | ~ l1_struct_0(X1_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_16]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_5063,plain,
% 11.72/2.00      ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
% 11.72/2.00      | ~ r1_tsep_1(sK5,sK4)
% 11.72/2.00      | ~ l1_struct_0(sK5)
% 11.72/2.00      | ~ l1_struct_0(sK4) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1895]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_27,plain,
% 11.72/2.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 11.72/2.00      | ~ m1_pre_topc(X1,X0)
% 11.72/2.00      | ~ v2_pre_topc(X0)
% 11.72/2.00      | v2_struct_0(X0)
% 11.72/2.00      | ~ l1_pre_topc(X0) ),
% 11.72/2.00      inference(cnf_transformation,[],[f102]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1884,plain,
% 11.72/2.00      ( v1_funct_2(k9_tmap_1(X0_60,X1_60),u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)))
% 11.72/2.00      | ~ m1_pre_topc(X1_60,X0_60)
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_27]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_6453,plain,
% 11.72/2.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 11.72/2.00      | ~ m1_pre_topc(sK4,sK3)
% 11.72/2.00      | ~ v2_pre_topc(sK3)
% 11.72/2.00      | v2_struct_0(sK3)
% 11.72/2.00      | ~ l1_pre_topc(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1884]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_6454,plain,
% 11.72/2.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
% 11.72/2.00      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_6453]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_26,plain,
% 11.72/2.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 11.72/2.00      | ~ m1_pre_topc(X1,X0)
% 11.72/2.00      | ~ v2_pre_topc(X0)
% 11.72/2.00      | v2_struct_0(X0)
% 11.72/2.00      | ~ l1_pre_topc(X0) ),
% 11.72/2.00      inference(cnf_transformation,[],[f103]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1885,plain,
% 11.72/2.00      ( m1_subset_1(k9_tmap_1(X0_60,X1_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)))))
% 11.72/2.00      | ~ m1_pre_topc(X1_60,X0_60)
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_26]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2825,plain,
% 11.72/2.00      ( m1_subset_1(k9_tmap_1(X0_60,X1_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60))))) = iProver_top
% 11.72/2.00      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_18,plain,
% 11.72/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.72/2.00      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 11.72/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.72/2.00      | ~ v1_funct_1(X0)
% 11.72/2.00      | ~ l1_struct_0(X1)
% 11.72/2.00      | ~ l1_struct_0(X2)
% 11.72/2.00      | ~ l1_struct_0(X3) ),
% 11.72/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1893,plain,
% 11.72/2.00      ( ~ v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60))
% 11.72/2.00      | v1_funct_2(k2_tmap_1(X0_60,X1_60,X0_59,X2_60),u1_struct_0(X2_60),u1_struct_0(X1_60))
% 11.72/2.00      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60))))
% 11.72/2.00      | ~ v1_funct_1(X0_59)
% 11.72/2.00      | ~ l1_struct_0(X0_60)
% 11.72/2.00      | ~ l1_struct_0(X1_60)
% 11.72/2.00      | ~ l1_struct_0(X2_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_18]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2817,plain,
% 11.72/2.00      ( v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60)) != iProver_top
% 11.72/2.00      | v1_funct_2(k2_tmap_1(X0_60,X1_60,X0_59,X2_60),u1_struct_0(X2_60),u1_struct_0(X1_60)) = iProver_top
% 11.72/2.00      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60)))) != iProver_top
% 11.72/2.00      | v1_funct_1(X0_59) != iProver_top
% 11.72/2.00      | l1_struct_0(X0_60) != iProver_top
% 11.72/2.00      | l1_struct_0(X1_60) != iProver_top
% 11.72/2.00      | l1_struct_0(X2_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1893]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_17,plain,
% 11.72/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.72/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.72/2.00      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 11.72/2.00      | ~ v1_funct_1(X0)
% 11.72/2.00      | ~ l1_struct_0(X1)
% 11.72/2.00      | ~ l1_struct_0(X2)
% 11.72/2.00      | ~ l1_struct_0(X3) ),
% 11.72/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1894,plain,
% 11.72/2.00      ( ~ v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60))
% 11.72/2.00      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60))))
% 11.72/2.00      | m1_subset_1(k2_tmap_1(X0_60,X1_60,X0_59,X2_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_60),u1_struct_0(X1_60))))
% 11.72/2.00      | ~ v1_funct_1(X0_59)
% 11.72/2.00      | ~ l1_struct_0(X0_60)
% 11.72/2.00      | ~ l1_struct_0(X1_60)
% 11.72/2.00      | ~ l1_struct_0(X2_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_17]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2816,plain,
% 11.72/2.00      ( v1_funct_2(X0_59,u1_struct_0(X0_60),u1_struct_0(X1_60)) != iProver_top
% 11.72/2.00      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_60),u1_struct_0(X1_60)))) != iProver_top
% 11.72/2.00      | m1_subset_1(k2_tmap_1(X0_60,X1_60,X0_59,X2_60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_60),u1_struct_0(X1_60)))) = iProver_top
% 11.72/2.00      | v1_funct_1(X0_59) != iProver_top
% 11.72/2.00      | l1_struct_0(X0_60) != iProver_top
% 11.72/2.00      | l1_struct_0(X1_60) != iProver_top
% 11.72/2.00      | l1_struct_0(X2_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_36,plain,
% 11.72/2.00      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
% 11.72/2.00      | ~ r1_xboole_0(u1_struct_0(X2),X1)
% 11.72/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.72/2.00      | ~ m1_pre_topc(X2,X0)
% 11.72/2.00      | ~ v2_pre_topc(X0)
% 11.72/2.00      | v2_struct_0(X0)
% 11.72/2.00      | v2_struct_0(X2)
% 11.72/2.00      | ~ l1_pre_topc(X0) ),
% 11.72/2.00      inference(cnf_transformation,[],[f112]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_42,negated_conjecture,
% 11.72/2.00      ( ~ v5_pre_topc(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),sK5,k8_tmap_1(sK3,sK4))
% 11.72/2.00      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 11.72/2.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 11.72/2.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) ),
% 11.72/2.00      inference(cnf_transformation,[],[f125]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_566,plain,
% 11.72/2.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 11.72/2.00      | ~ r1_xboole_0(u1_struct_0(X0),X1)
% 11.72/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 11.72/2.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 11.72/2.00      | ~ m1_pre_topc(X0,X2)
% 11.72/2.00      | ~ v2_pre_topc(X2)
% 11.72/2.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 11.72/2.00      | v2_struct_0(X2)
% 11.72/2.00      | v2_struct_0(X0)
% 11.72/2.00      | ~ l1_pre_topc(X2)
% 11.72/2.00      | k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),X0) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 11.72/2.00      | k6_tmap_1(X2,X1) != k8_tmap_1(sK3,sK4)
% 11.72/2.00      | sK5 != X0 ),
% 11.72/2.00      inference(resolution_lifted,[status(thm)],[c_36,c_42]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_567,plain,
% 11.72/2.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 11.72/2.00      | ~ r1_xboole_0(u1_struct_0(sK5),X0)
% 11.72/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/2.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 11.72/2.00      | ~ m1_pre_topc(sK5,X1)
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | v2_struct_0(sK5)
% 11.72/2.00      | ~ l1_pre_topc(X1)
% 11.72/2.00      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 11.72/2.00      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4) ),
% 11.72/2.00      inference(unflattening,[status(thm)],[c_566]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_45,negated_conjecture,
% 11.72/2.00      ( ~ v2_struct_0(sK5) ),
% 11.72/2.00      inference(cnf_transformation,[],[f122]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_571,plain,
% 11.72/2.00      ( v2_struct_0(X1)
% 11.72/2.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | ~ m1_pre_topc(sK5,X1)
% 11.72/2.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 11.72/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/2.00      | ~ r1_xboole_0(u1_struct_0(sK5),X0)
% 11.72/2.00      | ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 11.72/2.00      | ~ l1_pre_topc(X1)
% 11.72/2.00      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 11.72/2.00      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4) ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_567,c_45]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_572,plain,
% 11.72/2.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 11.72/2.00      | ~ r1_xboole_0(u1_struct_0(sK5),X0)
% 11.72/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/2.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 11.72/2.00      | ~ m1_pre_topc(sK5,X1)
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1)
% 11.72/2.00      | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 11.72/2.00      | k6_tmap_1(X1,X0) != k8_tmap_1(sK3,sK4) ),
% 11.72/2.00      inference(renaming,[status(thm)],[c_571]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1862,plain,
% 11.72/2.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 11.72/2.00      | ~ r1_xboole_0(u1_struct_0(sK5),X0_59)
% 11.72/2.00      | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
% 11.72/2.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 11.72/2.00      | ~ m1_pre_topc(sK5,X0_60)
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60)
% 11.72/2.00      | k6_tmap_1(X0_60,X0_59) != k8_tmap_1(sK3,sK4)
% 11.72/2.00      | k2_tmap_1(X0_60,k6_tmap_1(X0_60,X0_59),k7_tmap_1(X0_60,X0_59),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_572]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1911,plain,
% 11.72/2.00      ( ~ v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 11.72/2.00      | ~ m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 11.72/2.00      | ~ v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 11.72/2.00      | sP0_iProver_split ),
% 11.72/2.00      inference(splitting,
% 11.72/2.00                [splitting(split),new_symbols(definition,[])],
% 11.72/2.00                [c_1862]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2848,plain,
% 11.72/2.00      ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | m1_subset_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 11.72/2.00      | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) != iProver_top
% 11.72/2.00      | sP0_iProver_split = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1911]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_6492,plain,
% 11.72/2.00      ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 11.72/2.00      | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) != iProver_top
% 11.72/2.00      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 11.72/2.00      | l1_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top
% 11.72/2.00      | l1_struct_0(sK5) != iProver_top
% 11.72/2.00      | l1_struct_0(sK3) != iProver_top
% 11.72/2.00      | sP0_iProver_split = iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2816,c_2848]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3173,plain,
% 11.72/2.00      ( ~ v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))
% 11.72/2.00      | ~ m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 11.72/2.00      | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5))
% 11.72/2.00      | ~ v1_funct_1(k9_tmap_1(sK3,sK4))
% 11.72/2.00      | ~ l1_struct_0(k8_tmap_1(sK3,sK4))
% 11.72/2.00      | ~ l1_struct_0(sK5)
% 11.72/2.00      | ~ l1_struct_0(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1892]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3174,plain,
% 11.72/2.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 11.72/2.00      | v1_funct_1(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)) = iProver_top
% 11.72/2.00      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 11.72/2.00      | l1_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top
% 11.72/2.00      | l1_struct_0(sK5) != iProver_top
% 11.72/2.00      | l1_struct_0(sK3) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_3173]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3197,plain,
% 11.72/2.00      ( l1_pre_topc(sK5) != iProver_top
% 11.72/2.00      | l1_struct_0(sK5) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_3196]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3618,plain,
% 11.72/2.00      ( ~ l1_pre_topc(k8_tmap_1(sK3,X0_60))
% 11.72/2.00      | l1_struct_0(k8_tmap_1(sK3,X0_60)) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1909]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_4263,plain,
% 11.72/2.00      ( ~ l1_pre_topc(k8_tmap_1(sK3,sK4))
% 11.72/2.00      | l1_struct_0(k8_tmap_1(sK3,sK4)) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_3618]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_4264,plain,
% 11.72/2.00      ( l1_pre_topc(k8_tmap_1(sK3,sK4)) != iProver_top
% 11.72/2.00      | l1_struct_0(k8_tmap_1(sK3,sK4)) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_4263]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1888,plain,
% 11.72/2.00      ( ~ m1_pre_topc(X0_60,X1_60)
% 11.72/2.00      | ~ v2_pre_topc(X1_60)
% 11.72/2.00      | v2_struct_0(X1_60)
% 11.72/2.00      | ~ l1_pre_topc(X1_60)
% 11.72/2.00      | l1_pre_topc(k8_tmap_1(X1_60,X0_60)) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_23]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_5296,plain,
% 11.72/2.00      ( ~ m1_pre_topc(sK4,sK3)
% 11.72/2.00      | ~ v2_pre_topc(sK3)
% 11.72/2.00      | v2_struct_0(sK3)
% 11.72/2.00      | l1_pre_topc(k8_tmap_1(sK3,sK4))
% 11.72/2.00      | ~ l1_pre_topc(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1888]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_5297,plain,
% 11.72/2.00      ( m1_pre_topc(sK4,sK3) != iProver_top
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(k8_tmap_1(sK3,sK4)) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_5296]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_6623,plain,
% 11.72/2.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 11.72/2.00      | v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | sP0_iProver_split = iProver_top ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_6492,c_51,c_52,c_53,c_55,c_175,c_3174,c_3197,c_3551,
% 11.72/2.00                 c_3932,c_4264,c_5297,c_6454]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_6624,plain,
% 11.72/2.00      ( v1_funct_2(k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5),u1_struct_0(sK5),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 11.72/2.00      | sP0_iProver_split = iProver_top ),
% 11.72/2.00      inference(renaming,[status(thm)],[c_6623]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_6627,plain,
% 11.72/2.00      ( v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 11.72/2.00      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 11.72/2.00      | l1_struct_0(k8_tmap_1(sK3,sK4)) != iProver_top
% 11.72/2.00      | l1_struct_0(sK5) != iProver_top
% 11.72/2.00      | l1_struct_0(sK3) != iProver_top
% 11.72/2.00      | sP0_iProver_split = iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2817,c_6624]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_6826,plain,
% 11.72/2.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 11.72/2.00      | sP0_iProver_split = iProver_top ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_6627,c_51,c_52,c_53,c_55,c_175,c_3197,c_3551,c_3932,
% 11.72/2.00                 c_4264,c_5297,c_6454]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_6830,plain,
% 11.72/2.00      ( m1_pre_topc(sK4,sK3) != iProver_top
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top
% 11.72/2.00      | sP0_iProver_split = iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2825,c_6826]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_6831,plain,
% 11.72/2.00      ( ~ m1_pre_topc(sK4,sK3)
% 11.72/2.00      | ~ v2_pre_topc(sK3)
% 11.72/2.00      | v2_struct_0(sK3)
% 11.72/2.00      | ~ l1_pre_topc(sK3)
% 11.72/2.00      | sP0_iProver_split ),
% 11.72/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_6830]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_7133,plain,
% 11.72/2.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.72/2.00      | ~ m1_pre_topc(sK4,sK3)
% 11.72/2.00      | ~ l1_pre_topc(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_7131]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_8321,plain,
% 11.72/2.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)))))
% 11.72/2.00      | ~ m1_pre_topc(sK4,sK3)
% 11.72/2.00      | ~ v2_pre_topc(sK3)
% 11.72/2.00      | v2_struct_0(sK3)
% 11.72/2.00      | ~ l1_pre_topc(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1885]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_8322,plain,
% 11.72/2.00      ( m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) = iProver_top
% 11.72/2.00      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_8321]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_21,plain,
% 11.72/2.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 11.72/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.72/2.00      | ~ v2_pre_topc(X0)
% 11.72/2.00      | v2_struct_0(X0)
% 11.72/2.00      | ~ l1_pre_topc(X0) ),
% 11.72/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1890,plain,
% 11.72/2.00      ( v1_funct_2(k7_tmap_1(X0_60,X0_59),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_59)))
% 11.72/2.00      | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_21]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2820,plain,
% 11.72/2.00      ( v1_funct_2(k7_tmap_1(X0_60,X0_59),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,X0_59))) = iProver_top
% 11.72/2.00      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1890]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_8858,plain,
% 11.72/2.00      ( v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top
% 11.72/2.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_8848,c_2820]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1910,plain,
% 11.72/2.00      ( ~ r1_xboole_0(u1_struct_0(sK5),X0_59)
% 11.72/2.00      | ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
% 11.72/2.00      | ~ m1_pre_topc(sK5,X0_60)
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60)
% 11.72/2.00      | k6_tmap_1(X0_60,X0_59) != k8_tmap_1(sK3,sK4)
% 11.72/2.00      | k2_tmap_1(X0_60,k6_tmap_1(X0_60,X0_59),k7_tmap_1(X0_60,X0_59),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 11.72/2.00      | ~ sP0_iProver_split ),
% 11.72/2.00      inference(splitting,
% 11.72/2.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 11.72/2.00                [c_1862]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_9829,plain,
% 11.72/2.00      ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
% 11.72/2.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(X0_60)))
% 11.72/2.00      | ~ m1_pre_topc(sK5,X0_60)
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60)
% 11.72/2.00      | ~ sP0_iProver_split
% 11.72/2.00      | k6_tmap_1(X0_60,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 11.72/2.00      | k2_tmap_1(X0_60,k6_tmap_1(X0_60,u1_struct_0(sK4)),k7_tmap_1(X0_60,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1910]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_9831,plain,
% 11.72/2.00      ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
% 11.72/2.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.72/2.00      | ~ m1_pre_topc(sK5,sK3)
% 11.72/2.00      | ~ v2_pre_topc(sK3)
% 11.72/2.00      | v2_struct_0(sK3)
% 11.72/2.00      | ~ l1_pre_topc(sK3)
% 11.72/2.00      | ~ sP0_iProver_split
% 11.72/2.00      | k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 11.72/2.00      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) != k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_9829]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_14,plain,
% 11.72/2.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 11.72/2.00      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 11.72/2.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 11.72/2.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 11.72/2.00      | ~ m1_pre_topc(X1,X0)
% 11.72/2.00      | ~ v2_pre_topc(X0)
% 11.72/2.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 11.72/2.00      | v2_struct_0(X0)
% 11.72/2.00      | ~ l1_pre_topc(X0) ),
% 11.72/2.00      inference(cnf_transformation,[],[f130]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_315,plain,
% 11.72/2.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
% 11.72/2.00      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 11.72/2.00      | ~ m1_pre_topc(X1,X0)
% 11.72/2.00      | ~ v2_pre_topc(X0)
% 11.72/2.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 11.72/2.00      | v2_struct_0(X0)
% 11.72/2.00      | ~ l1_pre_topc(X0) ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_14,c_27,c_26]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1864,plain,
% 11.72/2.00      ( r1_funct_2(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))),k9_tmap_1(X0_60,X1_60),k7_tmap_1(X0_60,u1_struct_0(X1_60)))
% 11.72/2.00      | ~ m1_subset_1(u1_struct_0(X1_60),k1_zfmisc_1(u1_struct_0(X0_60)))
% 11.72/2.00      | ~ m1_pre_topc(X1_60,X0_60)
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | ~ v1_funct_1(k9_tmap_1(X0_60,X1_60))
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_315]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2846,plain,
% 11.72/2.00      ( r1_funct_2(u1_struct_0(X0_60),u1_struct_0(k8_tmap_1(X0_60,X1_60)),u1_struct_0(X0_60),u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))),k9_tmap_1(X0_60,X1_60),k7_tmap_1(X0_60,u1_struct_0(X1_60))) = iProver_top
% 11.72/2.00      | m1_subset_1(u1_struct_0(X1_60),k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
% 11.72/2.00      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v1_funct_1(k9_tmap_1(X0_60,X1_60)) != iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1864]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_8860,plain,
% 11.72/2.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top
% 11.72/2.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.72/2.00      | m1_pre_topc(sK4,sK3) != iProver_top
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_8848,c_2846]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_10008,plain,
% 11.72/2.00      ( r1_funct_2(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4)),k9_tmap_1(sK3,sK4),k7_tmap_1(sK3,u1_struct_0(sK4))) = iProver_top ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_8860,c_51,c_52,c_53,c_55,c_3932,c_7134]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_5,plain,
% 11.72/2.00      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 11.72/2.00      | ~ v1_funct_2(X5,X2,X3)
% 11.72/2.00      | ~ v1_funct_2(X4,X0,X1)
% 11.72/2.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.72/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.72/2.00      | ~ v1_funct_1(X5)
% 11.72/2.00      | ~ v1_funct_1(X4)
% 11.72/2.00      | v1_xboole_0(X1)
% 11.72/2.00      | v1_xboole_0(X3)
% 11.72/2.00      | X4 = X5 ),
% 11.72/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1904,plain,
% 11.72/2.00      ( ~ r1_funct_2(X0_59,X1_59,X2_59,X3_59,X4_59,X5_59)
% 11.72/2.00      | ~ v1_funct_2(X5_59,X2_59,X3_59)
% 11.72/2.00      | ~ v1_funct_2(X4_59,X0_59,X1_59)
% 11.72/2.00      | ~ m1_subset_1(X5_59,k1_zfmisc_1(k2_zfmisc_1(X2_59,X3_59)))
% 11.72/2.00      | ~ m1_subset_1(X4_59,k1_zfmisc_1(k2_zfmisc_1(X0_59,X1_59)))
% 11.72/2.00      | ~ v1_funct_1(X5_59)
% 11.72/2.00      | ~ v1_funct_1(X4_59)
% 11.72/2.00      | v1_xboole_0(X1_59)
% 11.72/2.00      | v1_xboole_0(X3_59)
% 11.72/2.00      | X4_59 = X5_59 ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_5]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2806,plain,
% 11.72/2.00      ( X0_59 = X1_59
% 11.72/2.00      | r1_funct_2(X2_59,X3_59,X4_59,X5_59,X0_59,X1_59) != iProver_top
% 11.72/2.00      | v1_funct_2(X0_59,X2_59,X3_59) != iProver_top
% 11.72/2.00      | v1_funct_2(X1_59,X4_59,X5_59) != iProver_top
% 11.72/2.00      | m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X2_59,X3_59))) != iProver_top
% 11.72/2.00      | m1_subset_1(X1_59,k1_zfmisc_1(k2_zfmisc_1(X4_59,X5_59))) != iProver_top
% 11.72/2.00      | v1_funct_1(X0_59) != iProver_top
% 11.72/2.00      | v1_funct_1(X1_59) != iProver_top
% 11.72/2.00      | v1_xboole_0(X5_59) = iProver_top
% 11.72/2.00      | v1_xboole_0(X3_59) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1904]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_10012,plain,
% 11.72/2.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k9_tmap_1(sK3,sK4)
% 11.72/2.00      | v1_funct_2(k9_tmap_1(sK3,sK4),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | v1_funct_2(k7_tmap_1(sK3,u1_struct_0(sK4)),u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | m1_subset_1(k9_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 11.72/2.00      | m1_subset_1(k7_tmap_1(sK3,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(k8_tmap_1(sK3,sK4))))) != iProver_top
% 11.72/2.00      | v1_funct_1(k9_tmap_1(sK3,sK4)) != iProver_top
% 11.72/2.00      | v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top
% 11.72/2.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) = iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_10008,c_2806]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2835,plain,
% 11.72/2.00      ( m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(X1_60))) = iProver_top
% 11.72/2.00      | m1_pre_topc(X0_60,X1_60) != iProver_top
% 11.72/2.00      | l1_pre_topc(X1_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1875]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_34,plain,
% 11.72/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1)
% 11.72/2.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 11.72/2.00      inference(cnf_transformation,[],[f108]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1879,plain,
% 11.72/2.00      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60)
% 11.72/2.00      | u1_struct_0(k6_tmap_1(X0_60,X0_59)) = u1_struct_0(X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_34]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2831,plain,
% 11.72/2.00      ( u1_struct_0(k6_tmap_1(X0_60,X0_59)) = u1_struct_0(X0_60)
% 11.72/2.00      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1879]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_4892,plain,
% 11.72/2.00      ( u1_struct_0(k6_tmap_1(X0_60,u1_struct_0(X1_60))) = u1_struct_0(X0_60)
% 11.72/2.00      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2835,c_2831]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_12637,plain,
% 11.72/2.00      ( u1_struct_0(k6_tmap_1(sK3,u1_struct_0(sK4))) = u1_struct_0(sK3)
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2841,c_4892]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_12650,plain,
% 11.72/2.00      ( u1_struct_0(k8_tmap_1(sK3,sK4)) = u1_struct_0(sK3)
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(light_normalisation,[status(thm)],[c_12637,c_8848]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1940,plain,
% 11.72/2.00      ( X0_60 != X1_60
% 11.72/2.00      | X2_60 != X3_60
% 11.72/2.00      | X4_60 != X5_60
% 11.72/2.00      | X0_59 != X1_59
% 11.72/2.00      | k2_tmap_1(X0_60,X2_60,X0_59,X4_60) = k2_tmap_1(X1_60,X3_60,X1_59,X5_60) ),
% 11.72/2.00      theory(equality) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_17657,plain,
% 11.72/2.00      ( X0_60 != sK3
% 11.72/2.00      | k6_tmap_1(X0_60,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 11.72/2.00      | sK5 != sK5
% 11.72/2.00      | k2_tmap_1(X0_60,k6_tmap_1(X0_60,u1_struct_0(sK4)),k7_tmap_1(X0_60,u1_struct_0(sK4)),sK5) = k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 11.72/2.00      | k7_tmap_1(X0_60,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1940]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_17658,plain,
% 11.72/2.00      ( k6_tmap_1(sK3,u1_struct_0(sK4)) != k8_tmap_1(sK3,sK4)
% 11.72/2.00      | sK5 != sK5
% 11.72/2.00      | sK3 != sK3
% 11.72/2.00      | k2_tmap_1(sK3,k6_tmap_1(sK3,u1_struct_0(sK4)),k7_tmap_1(sK3,u1_struct_0(sK4)),sK5) = k2_tmap_1(sK3,k8_tmap_1(sK3,sK4),k9_tmap_1(sK3,sK4),sK5)
% 11.72/2.00      | k7_tmap_1(sK3,u1_struct_0(sK4)) != k9_tmap_1(sK3,sK4) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_17657]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1923,plain,
% 11.72/2.00      ( ~ v1_xboole_0(X0_59) | v1_xboole_0(X1_59) | X1_59 != X0_59 ),
% 11.72/2.00      theory(equality) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3182,plain,
% 11.72/2.00      ( ~ v1_xboole_0(X0_59)
% 11.72/2.00      | v1_xboole_0(u1_struct_0(sK3))
% 11.72/2.00      | u1_struct_0(sK3) != X0_59 ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1923]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_18005,plain,
% 11.72/2.00      ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4)))
% 11.72/2.00      | v1_xboole_0(u1_struct_0(sK3))
% 11.72/2.00      | u1_struct_0(sK3) != u1_struct_0(k8_tmap_1(sK3,sK4)) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_3182]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_18006,plain,
% 11.72/2.00      ( u1_struct_0(sK3) != u1_struct_0(k8_tmap_1(sK3,sK4))
% 11.72/2.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK3,sK4))) != iProver_top
% 11.72/2.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_18005]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1917,plain,
% 11.72/2.00      ( X0_59 != X1_59 | X2_59 != X1_59 | X2_59 = X0_59 ),
% 11.72/2.00      theory(equality) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3639,plain,
% 11.72/2.00      ( X0_59 != X1_59
% 11.72/2.00      | u1_struct_0(sK3) != X1_59
% 11.72/2.00      | u1_struct_0(sK3) = X0_59 ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1917]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3964,plain,
% 11.72/2.00      ( X0_59 != u1_struct_0(sK3)
% 11.72/2.00      | u1_struct_0(sK3) = X0_59
% 11.72/2.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_3639]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_4569,plain,
% 11.72/2.00      ( u1_struct_0(X0_60) != u1_struct_0(sK3)
% 11.72/2.00      | u1_struct_0(sK3) = u1_struct_0(X0_60)
% 11.72/2.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_3964]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_19821,plain,
% 11.72/2.00      ( u1_struct_0(k8_tmap_1(sK3,sK4)) != u1_struct_0(sK3)
% 11.72/2.00      | u1_struct_0(sK3) = u1_struct_0(k8_tmap_1(sK3,sK4))
% 11.72/2.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_4569]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_28770,plain,
% 11.72/2.00      ( v1_funct_1(k7_tmap_1(sK3,u1_struct_0(sK4))) != iProver_top ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_9050,c_50,c_51,c_49,c_52,c_48,c_53,c_46,c_55,c_44,
% 11.72/2.00                 c_168,c_175,c_1944,c_1966,c_3193,c_3196,c_3555,c_3556,
% 11.72/2.00                 c_3881,c_3932,c_4557,c_5063,c_6454,c_6831,c_7133,c_7134,
% 11.72/2.00                 c_8322,c_8621,c_8857,c_8858,c_9831,c_10012,c_12650,
% 11.72/2.00                 c_17658,c_18006,c_19821]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_6,plain,
% 11.72/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1)
% 11.72/2.00      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 11.72/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1903,plain,
% 11.72/2.00      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60)
% 11.72/2.00      | k7_tmap_1(X0_60,X0_59) = k6_partfun1(u1_struct_0(X0_60)) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_6]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2807,plain,
% 11.72/2.00      ( k7_tmap_1(X0_60,X0_59) = k6_partfun1(u1_struct_0(X0_60))
% 11.72/2.00      | m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_4805,plain,
% 11.72/2.00      ( k7_tmap_1(X0_60,u1_struct_0(X1_60)) = k6_partfun1(u1_struct_0(X0_60))
% 11.72/2.00      | m1_pre_topc(X1_60,X0_60) != iProver_top
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2835,c_2807]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_11250,plain,
% 11.72/2.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3))
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2841,c_4805]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_11444,plain,
% 11.72/2.00      ( k7_tmap_1(sK3,u1_struct_0(sK4)) = k6_partfun1(u1_struct_0(sK3)) ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_11250,c_51,c_52,c_53]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_28774,plain,
% 11.72/2.00      ( v1_funct_1(k6_partfun1(u1_struct_0(sK3))) != iProver_top ),
% 11.72/2.00      inference(light_normalisation,[status(thm)],[c_28770,c_11444]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1866,negated_conjecture,
% 11.72/2.00      ( v2_pre_topc(sK3) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_49]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2844,plain,
% 11.72/2.00      ( v2_pre_topc(sK3) = iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1866]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_40,plain,
% 11.72/2.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 11.72/2.00      inference(cnf_transformation,[],[f115]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1874,plain,
% 11.72/2.00      ( m1_pre_topc(X0_60,X0_60) | ~ l1_pre_topc(X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_40]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2836,plain,
% 11.72/2.00      ( m1_pre_topc(X0_60,X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1874]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_11251,plain,
% 11.72/2.00      ( k7_tmap_1(X0_60,u1_struct_0(X0_60)) = k6_partfun1(u1_struct_0(X0_60))
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2836,c_4805]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_11490,plain,
% 11.72/2.00      ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3))
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2844,c_11251]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_62,plain,
% 11.72/2.00      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_40]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_65,plain,
% 11.72/2.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.72/2.00      | ~ m1_pre_topc(sK3,sK3)
% 11.72/2.00      | ~ l1_pre_topc(sK3) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_39]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2937,plain,
% 11.72/2.00      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.72/2.00      | ~ v2_pre_topc(sK3)
% 11.72/2.00      | v2_struct_0(sK3)
% 11.72/2.00      | ~ l1_pre_topc(sK3)
% 11.72/2.00      | k7_tmap_1(sK3,X0_59) = k6_partfun1(u1_struct_0(sK3)) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_1903]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3326,plain,
% 11.72/2.00      ( ~ m1_subset_1(u1_struct_0(X0_60),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.72/2.00      | ~ v2_pre_topc(sK3)
% 11.72/2.00      | v2_struct_0(sK3)
% 11.72/2.00      | ~ l1_pre_topc(sK3)
% 11.72/2.00      | k7_tmap_1(sK3,u1_struct_0(X0_60)) = k6_partfun1(u1_struct_0(sK3)) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_2937]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_3328,plain,
% 11.72/2.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.72/2.00      | ~ v2_pre_topc(sK3)
% 11.72/2.00      | v2_struct_0(sK3)
% 11.72/2.00      | ~ l1_pre_topc(sK3)
% 11.72/2.00      | k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_3326]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_11563,plain,
% 11.72/2.00      ( k7_tmap_1(sK3,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK3)) ),
% 11.72/2.00      inference(global_propositional_subsumption,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_11490,c_50,c_49,c_48,c_62,c_65,c_3328]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_22,plain,
% 11.72/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/2.00      | ~ v2_pre_topc(X1)
% 11.72/2.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 11.72/2.00      | v2_struct_0(X1)
% 11.72/2.00      | ~ l1_pre_topc(X1) ),
% 11.72/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_1889,plain,
% 11.72/2.00      ( ~ m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60)))
% 11.72/2.00      | ~ v2_pre_topc(X0_60)
% 11.72/2.00      | v1_funct_1(k7_tmap_1(X0_60,X0_59))
% 11.72/2.00      | v2_struct_0(X0_60)
% 11.72/2.00      | ~ l1_pre_topc(X0_60) ),
% 11.72/2.00      inference(subtyping,[status(esa)],[c_22]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_2821,plain,
% 11.72/2.00      ( m1_subset_1(X0_59,k1_zfmisc_1(u1_struct_0(X0_60))) != iProver_top
% 11.72/2.00      | v2_pre_topc(X0_60) != iProver_top
% 11.72/2.00      | v1_funct_1(k7_tmap_1(X0_60,X0_59)) = iProver_top
% 11.72/2.00      | v2_struct_0(X0_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0_60) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_1889]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_4810,plain,
% 11.72/2.00      ( m1_pre_topc(X0_60,X1_60) != iProver_top
% 11.72/2.00      | v2_pre_topc(X1_60) != iProver_top
% 11.72/2.00      | v1_funct_1(k7_tmap_1(X1_60,u1_struct_0(X0_60))) = iProver_top
% 11.72/2.00      | v2_struct_0(X1_60) = iProver_top
% 11.72/2.00      | l1_pre_topc(X1_60) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_2835,c_2821]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_12099,plain,
% 11.72/2.00      ( m1_pre_topc(sK3,sK3) != iProver_top
% 11.72/2.00      | v2_pre_topc(sK3) != iProver_top
% 11.72/2.00      | v1_funct_1(k6_partfun1(u1_struct_0(sK3))) = iProver_top
% 11.72/2.00      | v2_struct_0(sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(superposition,[status(thm)],[c_11563,c_4810]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_61,plain,
% 11.72/2.00      ( m1_pre_topc(X0,X0) = iProver_top
% 11.72/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.72/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(c_63,plain,
% 11.72/2.00      ( m1_pre_topc(sK3,sK3) = iProver_top
% 11.72/2.00      | l1_pre_topc(sK3) != iProver_top ),
% 11.72/2.00      inference(instantiation,[status(thm)],[c_61]) ).
% 11.72/2.00  
% 11.72/2.00  cnf(contradiction,plain,
% 11.72/2.00      ( $false ),
% 11.72/2.00      inference(minisat,
% 11.72/2.00                [status(thm)],
% 11.72/2.00                [c_28774,c_12099,c_63,c_53,c_52,c_51]) ).
% 11.72/2.00  
% 11.72/2.00  
% 11.72/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.72/2.00  
% 11.72/2.00  ------                               Statistics
% 11.72/2.00  
% 11.72/2.00  ------ General
% 11.72/2.00  
% 11.72/2.00  abstr_ref_over_cycles:                  0
% 11.72/2.00  abstr_ref_under_cycles:                 0
% 11.72/2.00  gc_basic_clause_elim:                   0
% 11.72/2.00  forced_gc_time:                         0
% 11.72/2.00  parsing_time:                           0.011
% 11.72/2.00  unif_index_cands_time:                  0.
% 11.72/2.00  unif_index_add_time:                    0.
% 11.72/2.00  orderings_time:                         0.
% 11.72/2.00  out_proof_time:                         0.02
% 11.72/2.00  total_time:                             1.312
% 11.72/2.00  num_of_symbols:                         70
% 11.72/2.00  num_of_terms:                           37676
% 11.72/2.00  
% 11.72/2.00  ------ Preprocessing
% 11.72/2.00  
% 11.72/2.00  num_of_splits:                          1
% 11.72/2.00  num_of_split_atoms:                     1
% 11.72/2.00  num_of_reused_defs:                     0
% 11.72/2.00  num_eq_ax_congr_red:                    36
% 11.72/2.00  num_of_sem_filtered_clauses:            5
% 11.72/2.00  num_of_subtypes:                        4
% 11.72/2.00  monotx_restored_types:                  0
% 11.72/2.00  sat_num_of_epr_types:                   0
% 11.72/2.00  sat_num_of_non_cyclic_types:            0
% 11.72/2.00  sat_guarded_non_collapsed_types:        2
% 11.72/2.00  num_pure_diseq_elim:                    0
% 11.72/2.00  simp_replaced_by:                       0
% 11.72/2.00  res_preprocessed:                       250
% 11.72/2.00  prep_upred:                             0
% 11.72/2.00  prep_unflattend:                        51
% 11.72/2.00  smt_new_axioms:                         0
% 11.72/2.00  pred_elim_cands:                        13
% 11.72/2.00  pred_elim:                              1
% 11.72/2.00  pred_elim_cl:                           1
% 11.72/2.00  pred_elim_cycles:                       7
% 11.72/2.00  merged_defs:                            0
% 11.72/2.00  merged_defs_ncl:                        0
% 11.72/2.00  bin_hyper_res:                          0
% 11.72/2.00  prep_cycles:                            4
% 11.72/2.00  pred_elim_time:                         0.044
% 11.72/2.00  splitting_time:                         0.
% 11.72/2.00  sem_filter_time:                        0.
% 11.72/2.00  monotx_time:                            0.
% 11.72/2.00  subtype_inf_time:                       0.002
% 11.72/2.00  
% 11.72/2.00  ------ Problem properties
% 11.72/2.00  
% 11.72/2.00  clauses:                                49
% 11.72/2.00  conjectures:                            8
% 11.72/2.00  epr:                                    13
% 11.72/2.00  horn:                                   24
% 11.72/2.00  ground:                                 9
% 11.72/2.00  unary:                                  8
% 11.72/2.00  binary:                                 3
% 11.72/2.00  lits:                                   247
% 11.72/2.00  lits_eq:                                16
% 11.72/2.00  fd_pure:                                0
% 11.72/2.00  fd_pseudo:                              0
% 11.72/2.00  fd_cond:                                0
% 11.72/2.00  fd_pseudo_cond:                         7
% 11.72/2.00  ac_symbols:                             0
% 11.72/2.00  
% 11.72/2.00  ------ Propositional Solver
% 11.72/2.00  
% 11.72/2.00  prop_solver_calls:                      33
% 11.72/2.00  prop_fast_solver_calls:                 4816
% 11.72/2.00  smt_solver_calls:                       0
% 11.72/2.00  smt_fast_solver_calls:                  0
% 11.72/2.00  prop_num_of_clauses:                    10453
% 11.72/2.00  prop_preprocess_simplified:             22125
% 11.72/2.00  prop_fo_subsumed:                       492
% 11.72/2.00  prop_solver_time:                       0.
% 11.72/2.00  smt_solver_time:                        0.
% 11.72/2.00  smt_fast_solver_time:                   0.
% 11.72/2.00  prop_fast_solver_time:                  0.
% 11.72/2.00  prop_unsat_core_time:                   0.001
% 11.72/2.00  
% 11.72/2.00  ------ QBF
% 11.72/2.00  
% 11.72/2.00  qbf_q_res:                              0
% 11.72/2.00  qbf_num_tautologies:                    0
% 11.72/2.00  qbf_prep_cycles:                        0
% 11.72/2.00  
% 11.72/2.00  ------ BMC1
% 11.72/2.00  
% 11.72/2.00  bmc1_current_bound:                     -1
% 11.72/2.00  bmc1_last_solved_bound:                 -1
% 11.72/2.00  bmc1_unsat_core_size:                   -1
% 11.72/2.00  bmc1_unsat_core_parents_size:           -1
% 11.72/2.00  bmc1_merge_next_fun:                    0
% 11.72/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.72/2.00  
% 11.72/2.00  ------ Instantiation
% 11.72/2.00  
% 11.72/2.00  inst_num_of_clauses:                    2734
% 11.72/2.00  inst_num_in_passive:                    513
% 11.72/2.00  inst_num_in_active:                     1514
% 11.72/2.00  inst_num_in_unprocessed:                707
% 11.72/2.00  inst_num_of_loops:                      1640
% 11.72/2.00  inst_num_of_learning_restarts:          0
% 11.72/2.00  inst_num_moves_active_passive:          122
% 11.72/2.00  inst_lit_activity:                      0
% 11.72/2.00  inst_lit_activity_moves:                0
% 11.72/2.00  inst_num_tautologies:                   0
% 11.72/2.00  inst_num_prop_implied:                  0
% 11.72/2.00  inst_num_existing_simplified:           0
% 11.72/2.00  inst_num_eq_res_simplified:             0
% 11.72/2.00  inst_num_child_elim:                    0
% 11.72/2.00  inst_num_of_dismatching_blockings:      5152
% 11.72/2.00  inst_num_of_non_proper_insts:           5041
% 11.72/2.00  inst_num_of_duplicates:                 0
% 11.72/2.00  inst_inst_num_from_inst_to_res:         0
% 11.72/2.00  inst_dismatching_checking_time:         0.
% 11.72/2.00  
% 11.72/2.00  ------ Resolution
% 11.72/2.00  
% 11.72/2.00  res_num_of_clauses:                     0
% 11.72/2.00  res_num_in_passive:                     0
% 11.72/2.00  res_num_in_active:                      0
% 11.72/2.00  res_num_of_loops:                       254
% 11.72/2.00  res_forward_subset_subsumed:            88
% 11.72/2.00  res_backward_subset_subsumed:           0
% 11.72/2.00  res_forward_subsumed:                   0
% 11.72/2.00  res_backward_subsumed:                  0
% 11.72/2.00  res_forward_subsumption_resolution:     16
% 11.72/2.00  res_backward_subsumption_resolution:    0
% 11.72/2.00  res_clause_to_clause_subsumption:       2776
% 11.72/2.00  res_orphan_elimination:                 0
% 11.72/2.00  res_tautology_del:                      288
% 11.72/2.00  res_num_eq_res_simplified:              0
% 11.72/2.00  res_num_sel_changes:                    0
% 11.72/2.00  res_moves_from_active_to_pass:          0
% 11.72/2.00  
% 11.72/2.00  ------ Superposition
% 11.72/2.00  
% 11.72/2.00  sup_time_total:                         0.
% 11.72/2.00  sup_time_generating:                    0.
% 11.72/2.00  sup_time_sim_full:                      0.
% 11.72/2.00  sup_time_sim_immed:                     0.
% 11.72/2.00  
% 11.72/2.00  sup_num_of_clauses:                     738
% 11.72/2.00  sup_num_in_active:                      283
% 11.72/2.00  sup_num_in_passive:                     455
% 11.72/2.00  sup_num_of_loops:                       327
% 11.72/2.00  sup_fw_superposition:                   419
% 11.72/2.00  sup_bw_superposition:                   554
% 11.72/2.00  sup_immediate_simplified:               300
% 11.72/2.00  sup_given_eliminated:                   0
% 11.72/2.00  comparisons_done:                       0
% 11.72/2.00  comparisons_avoided:                    62
% 11.72/2.00  
% 11.72/2.00  ------ Simplifications
% 11.72/2.00  
% 11.72/2.00  
% 11.72/2.00  sim_fw_subset_subsumed:                 64
% 11.72/2.00  sim_bw_subset_subsumed:                 49
% 11.72/2.00  sim_fw_subsumed:                        20
% 11.72/2.00  sim_bw_subsumed:                        5
% 11.72/2.00  sim_fw_subsumption_res:                 0
% 11.72/2.00  sim_bw_subsumption_res:                 0
% 11.72/2.00  sim_tautology_del:                      36
% 11.72/2.00  sim_eq_tautology_del:                   7
% 11.72/2.00  sim_eq_res_simp:                        2
% 11.72/2.00  sim_fw_demodulated:                     0
% 11.72/2.00  sim_bw_demodulated:                     37
% 11.72/2.00  sim_light_normalised:                   241
% 11.72/2.00  sim_joinable_taut:                      0
% 11.72/2.00  sim_joinable_simp:                      0
% 11.72/2.00  sim_ac_normalised:                      0
% 11.72/2.00  sim_smt_subsumption:                    0
% 11.72/2.00  
%------------------------------------------------------------------------------
