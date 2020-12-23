%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1802+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:28 EST 2020

% Result     : Theorem 11.35s
% Output     : CNFRefutation 11.35s
% Verified   : 
% Statistics : Number of formulae       :  226 (3314 expanded)
%              Number of clauses        :  142 ( 706 expanded)
%              Number of leaves         :   23 (1172 expanded)
%              Depth                    :   28
%              Number of atoms          : 1239 (26838 expanded)
%              Number of equality atoms :  375 (1502 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   20 (   5 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
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
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),sK5)
        & m1_subset_1(sK5,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_tsep_1(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tmap_1(sK4,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),sK4),X3)
            & m1_subset_1(X3,u1_struct_0(sK4)) )
        & r1_tsep_1(X1,sK4)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_tsep_1(sK3,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
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
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & r1_tsep_1(sK3,sK4)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f62,f75,f74,f73,f72])).

fof(f122,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f16,axiom,(
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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f125,plain,(
    ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f76])).

fof(f121,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f76])).

fof(f124,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f76])).

fof(f116,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f117,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f118,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f1,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK0(X0,X1,X2)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f64,f65])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f66])).

fof(f126,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f127,plain,(
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
    inference(equality_resolution,[],[f126])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f120,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f110,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f119,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f2,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f68,plain,(
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
    inference(rectify,[],[f67])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
                    & u1_struct_0(X1) = sK1(X0,X1,X2)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f68,f69])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f107,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f100,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k9_tmap_1(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f123,plain,(
    r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f76])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f101,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,plain,
    ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tsep_1(X0,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_42,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_32,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X3)
    | ~ r1_xboole_0(u1_struct_0(X0),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_39,negated_conjecture,
    ( ~ r1_tmap_1(sK4,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_571,plain,
    ( ~ r1_xboole_0(u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),X0) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X2,X1) != k8_tmap_1(sK2,sK3)
    | sK5 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_39])).

cnf(c_572,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_576,plain,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_43,c_40])).

cnf(c_577,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(sK4,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_576])).

cnf(c_1729,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(X1,X0) != k8_tmap_1(sK2,sK3)
    | sK2 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_577])).

cnf(c_1730,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1729])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1734,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1730,c_48,c_47,c_46])).

cnf(c_1735,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X0),k7_tmap_1(sK2,X0),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_1734])).

cnf(c_1896,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,X2),k7_tmap_1(sK2,X2),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,X2) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X1) != X2
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_1735])).

cnf(c_1897,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(X1)),k7_tmap_1(sK2,u1_struct_0(X1)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(X1)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1896])).

cnf(c_2411,plain,
    ( ~ r1_tsep_1(X0_62,X1_62)
    | ~ m1_subset_1(u1_struct_0(X1_62),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X1_62)
    | ~ l1_struct_0(X0_62)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(X1_62)),k7_tmap_1(sK2,u1_struct_0(X1_62)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(X1_62)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X0_62) != u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_1897])).

cnf(c_34406,plain,
    ( ~ r1_tsep_1(X0_62,sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(X0_62)
    | ~ l1_struct_0(sK3)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(X0_62) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2411])).

cnf(c_35232,plain,
    ( ~ r1_tsep_1(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK4)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK4) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_34406])).

cnf(c_3,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_35,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_324,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_35,c_19,c_18,c_17])).

cnf(c_325,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_44,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1411,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_325,c_44])).

cnf(c_1412,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1411])).

cnf(c_1414,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1412,c_48,c_47,c_46])).

cnf(c_2428,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_1414])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2461,plain,
    ( ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_62)))
    | m1_subset_1(k7_tmap_1(X0_62,X0_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_62),u1_struct_0(k6_tmap_1(X0_62,X0_61)))))
    | v2_struct_0(X0_62)
    | ~ v2_pre_topc(X0_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3398,plain,
    ( m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | m1_subset_1(k7_tmap_1(X0_62,X0_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_62),u1_struct_0(k6_tmap_1(X0_62,X0_61))))) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2461])).

cnf(c_4532,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2428,c_3398])).

cnf(c_34,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1440,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_44])).

cnf(c_1441,plain,
    ( v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1440])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1443,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1441,c_48,c_47,c_46,c_45])).

cnf(c_2425,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1443])).

cnf(c_4534,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4532,c_2425])).

cnf(c_49,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_50,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_51,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_1427,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_44])).

cnf(c_1428,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1427])).

cnf(c_1429,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_6007,plain,
    ( m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4534,c_49,c_50,c_51,c_1429])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1640,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k9_tmap_1(X1,X2) = X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_44])).

cnf(c_1641,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1640])).

cnf(c_1645,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1641,c_48,c_47,c_46])).

cnf(c_1646,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1645])).

cnf(c_2414,plain,
    ( ~ v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0_61)
    | sK1(sK2,sK3,X0_61) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0_61 ),
    inference(subtyping,[status(esa)],[c_1646])).

cnf(c_3439,plain,
    ( sK1(sK2,sK3,X0_61) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0_61
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_funct_1(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_3452,plain,
    ( sK1(sK2,sK3,X0_61) = u1_struct_0(sK3)
    | k9_tmap_1(sK2,sK3) = X0_61
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_61) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3439,c_2425])).

cnf(c_6268,plain,
    ( sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6007,c_3452])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2459,plain,
    ( ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_62)))
    | v1_funct_1(k7_tmap_1(X0_62,X0_61))
    | v2_struct_0(X0_62)
    | ~ v2_pre_topc(X0_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3571,plain,
    ( ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,X0_61))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2459])).

cnf(c_3830,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3571])).

cnf(c_3831,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3830])).

cnf(c_15,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2460,plain,
    ( v1_funct_2(k7_tmap_1(X0_62,X0_61),u1_struct_0(X0_62),u1_struct_0(k6_tmap_1(X0_62,X0_61)))
    | ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_62)))
    | v2_struct_0(X0_62)
    | ~ v2_pre_topc(X0_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3399,plain,
    ( v1_funct_2(k7_tmap_1(X0_62,X0_61),u1_struct_0(X0_62),u1_struct_0(k6_tmap_1(X0_62,X0_61))) = iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2460])).

cnf(c_4553,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2428,c_3399])).

cnf(c_4554,plain,
    ( v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4553,c_2425])).

cnf(c_9179,plain,
    ( sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6268,c_49,c_50,c_51,c_1429,c_3831,c_4554])).

cnf(c_30,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_4,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1209,plain,
    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK1(X0,X1,X2))),X2,k7_tmap_1(X0,sK1(X0,X1,X2)))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = X2
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_44])).

cnf(c_1210,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1209])).

cnf(c_1214,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1210,c_48,c_47,c_46])).

cnf(c_1215,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0))),X0,k7_tmap_1(sK2,sK1(sK2,sK3,X0)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1214])).

cnf(c_1967,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ v1_funct_2(X6,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X6)
    | X6 != X3
    | k7_tmap_1(sK2,sK1(sK2,sK3,X6)) != X3
    | k9_tmap_1(sK2,sK3) = X6
    | u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X6))) != X2
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != X5
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1215])).

cnf(c_1968,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1))))
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k7_tmap_1(sK2,sK1(sK2,sK3,X1)) != X1
    | k9_tmap_1(sK2,sK3) = X1 ),
    inference(unflattening,[status(thm)],[c_1967])).

cnf(c_2409,plain,
    ( ~ v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1_61))))
    | ~ v1_funct_2(X1_61,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1_61))))))
    | ~ m1_subset_1(X1_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X1_61))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(X0_61)
    | ~ v1_funct_1(X1_61)
    | k7_tmap_1(sK2,sK1(sK2,sK3,X1_61)) != X1_61
    | k9_tmap_1(sK2,sK3) = X1_61 ),
    inference(subtyping,[status(esa)],[c_1968])).

cnf(c_3444,plain,
    ( k7_tmap_1(sK2,sK1(sK2,sK3,X0_61)) != X0_61
    | k9_tmap_1(sK2,sK3) = X0_61
    | v1_funct_2(X1_61,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))) != iProver_top
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(X1_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))))) != iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top
    | v1_funct_1(X1_61) != iProver_top
    | v1_funct_1(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_3460,plain,
    ( k7_tmap_1(sK2,sK1(sK2,sK3,X0_61)) != X0_61
    | k9_tmap_1(sK2,sK3) = X0_61
    | v1_funct_2(X1_61,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))) != iProver_top
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))))) != iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_61) != iProver_top
    | v1_funct_1(X1_61) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3444,c_2425])).

cnf(c_25,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_96,plain,
    ( v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_98,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_23,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_100,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_102,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_6972,plain,
    ( v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))) = iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))))) != iProver_top
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(X1_61,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))) != iProver_top
    | k9_tmap_1(sK2,sK3) = X0_61
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0_61)) != X0_61
    | v1_funct_1(X0_61) != iProver_top
    | v1_funct_1(X1_61) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3460,c_49,c_51,c_98,c_102])).

cnf(c_6973,plain,
    ( k7_tmap_1(sK2,sK1(sK2,sK3,X0_61)) != X0_61
    | k9_tmap_1(sK2,sK3) = X0_61
    | v1_funct_2(X1_61,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))) != iProver_top
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))))) != iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,X0_61)))) = iProver_top
    | v1_funct_1(X0_61) != iProver_top
    | v1_funct_1(X1_61) != iProver_top ),
    inference(renaming,[status(thm)],[c_6972])).

cnf(c_9181,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))))) != iProver_top
    | m1_subset_1(k7_tmap_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))) = iProver_top
    | v1_funct_1(X0_61) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9179,c_6973])).

cnf(c_33802,plain,
    ( v1_funct_1(X0_61) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))) = iProver_top
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9181,c_49,c_50,c_51,c_1429,c_3831,c_4534,c_4554])).

cnf(c_33803,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))) = iProver_top
    | v1_funct_1(X0_61) != iProver_top ),
    inference(renaming,[status(thm)],[c_33802])).

cnf(c_33808,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))) = iProver_top
    | v1_funct_1(k7_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3398,c_33803])).

cnf(c_3569,plain,
    ( v1_funct_2(k7_tmap_1(sK2,X0_61),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,X0_61)))
    | ~ m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2460])).

cnf(c_8020,plain,
    ( v1_funct_2(k7_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(X0_62,u1_struct_0(sK3)))),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(X0_62,u1_struct_0(sK3))))))
    | ~ m1_subset_1(sK1(sK2,sK3,k7_tmap_1(X0_62,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3569])).

cnf(c_8046,plain,
    ( v1_funct_2(k7_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(X0_62,u1_struct_0(sK3)))),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(X0_62,u1_struct_0(sK3)))))) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,k7_tmap_1(X0_62,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8020])).

cnf(c_8048,plain,
    ( v1_funct_2(k7_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8046])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1613,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_tmap_1(X1,X2) = X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_44])).

cnf(c_1614,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1613])).

cnf(c_1618,plain,
    ( ~ v1_funct_1(X0)
    | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1614,c_48,c_47,c_46])).

cnf(c_1619,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | k9_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1618])).

cnf(c_2415,plain,
    ( ~ v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | m1_subset_1(sK1(sK2,sK3,X0_61),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_61)
    | k9_tmap_1(sK2,sK3) = X0_61 ),
    inference(subtyping,[status(esa)],[c_1619])).

cnf(c_3438,plain,
    ( k9_tmap_1(sK2,sK3) = X0_61
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,X0_61),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(X0_61) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2415])).

cnf(c_3454,plain,
    ( k9_tmap_1(sK2,sK3) = X0_61
    | v1_funct_2(X0_61,u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,X0_61),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(X0_61) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3438,c_2425])).

cnf(c_6289,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_2(k7_tmap_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6007,c_3454])).

cnf(c_9626,plain,
    ( m1_subset_1(sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6289,c_49,c_50,c_51,c_1429,c_3831,c_4554])).

cnf(c_9627,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | m1_subset_1(sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9626])).

cnf(c_3400,plain,
    ( m1_subset_1(X0_61,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_62,X0_61)) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2459])).

cnf(c_9634,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_1(k7_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9627,c_3400])).

cnf(c_13011,plain,
    ( v1_funct_1(k7_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))))) = iProver_top
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9634,c_49,c_50,c_51])).

cnf(c_13012,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_funct_1(k7_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_13011])).

cnf(c_33847,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k7_tmap_1(sK2,u1_struct_0(sK3)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33808,c_49,c_50,c_51,c_8048,c_9627,c_13012])).

cnf(c_33854,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9179,c_33847])).

cnf(c_33856,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k9_tmap_1(sK2,sK3)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33854,c_2425,c_2428])).

cnf(c_2481,plain,
    ( X0_62 != X1_62
    | u1_struct_0(X0_62) = u1_struct_0(X1_62) ),
    theory(equality)).

cnf(c_5210,plain,
    ( X0_62 != sK4
    | u1_struct_0(X0_62) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2481])).

cnf(c_6762,plain,
    ( sK4 != sK4
    | u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5210])).

cnf(c_2467,plain,
    ( X0_62 = X0_62 ),
    theory(equality)).

cnf(c_4702,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2467])).

cnf(c_2491,plain,
    ( k2_tmap_1(X0_62,X1_62,X0_61,X2_62) = k2_tmap_1(X3_62,X4_62,X1_61,X5_62)
    | X0_62 != X3_62
    | X1_62 != X4_62
    | X2_62 != X5_62
    | X0_61 != X1_61 ),
    theory(equality)).

cnf(c_4373,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK4) = k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK4)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK2 != sK2
    | sK4 != sK4
    | k7_tmap_1(sK2,u1_struct_0(sK3)) != k9_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2491])).

cnf(c_41,negated_conjecture,
    ( r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2452,negated_conjecture,
    ( r1_tsep_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_3407,plain,
    ( r1_tsep_1(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2452])).

cnf(c_31,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2454,plain,
    ( ~ r1_tsep_1(X0_62,X1_62)
    | r1_tsep_1(X1_62,X0_62)
    | ~ l1_struct_0(X1_62)
    | ~ l1_struct_0(X0_62) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_3405,plain,
    ( r1_tsep_1(X0_62,X1_62) != iProver_top
    | r1_tsep_1(X1_62,X0_62) = iProver_top
    | l1_struct_0(X1_62) != iProver_top
    | l1_struct_0(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2454])).

cnf(c_3928,plain,
    ( r1_tsep_1(sK4,sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3407,c_3405])).

cnf(c_3929,plain,
    ( r1_tsep_1(sK4,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3928])).

cnf(c_2458,plain,
    ( l1_struct_0(X0_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3805,plain,
    ( l1_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2458])).

cnf(c_3802,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2458])).

cnf(c_2520,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2467])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1448,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_44])).

cnf(c_1449,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1448])).

cnf(c_1300,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_42])).

cnf(c_1301,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1300])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35232,c_33856,c_6762,c_4702,c_4373,c_3929,c_3805,c_3802,c_2428,c_2520,c_1449,c_1428,c_1301,c_102,c_98,c_51,c_46,c_49])).


%------------------------------------------------------------------------------
