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
% DateTime   : Thu Dec  3 12:22:41 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  279 (2292 expanded)
%              Number of clauses        :  181 ( 414 expanded)
%              Number of leaves         :   22 ( 871 expanded)
%              Depth                    :   29
%              Number of atoms          : 1837 (34155 expanded)
%              Number of equality atoms :  300 (2540 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK1(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK1(X0,X1,X2))
                    & r1_tarski(sK1(X0,X1,X2),X2)
                    & v3_pre_topc(sK1(X0,X1,X2),X0)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
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
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK7 = X4
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                | ~ r1_tmap_1(X1,X0,X2,X4) )
              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                | r1_tmap_1(X1,X0,X2,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | ~ r1_tmap_1(X1,X0,X2,sK6) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK6) )
            & sK6 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                    | ~ r1_tmap_1(X1,X0,X2,X4) )
                  & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                    | r1_tmap_1(X1,X0,X2,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_pre_topc(X3,X1)
          & v1_tsep_1(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK5)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK5,X1)
        & v1_tsep_1(sK5,X1)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                        | ~ r1_tmap_1(X1,X0,X2,X4) )
                      & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                        | r1_tmap_1(X1,X0,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_pre_topc(X3,X1)
              & v1_tsep_1(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK4,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5)
                      | r1_tmap_1(X1,X0,sK4,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK3,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5)
                          | r1_tmap_1(sK3,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK3)) )
                & m1_pre_topc(X3,sK3)
                & v1_tsep_1(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | r1_tmap_1(X1,X0,X2,X4) )
                            & X4 = X5
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
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
                          ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK2,X2,X4) )
                          & ( r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                            | r1_tmap_1(X1,sK2,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
      | ~ r1_tmap_1(sK3,sK2,sK4,sK6) )
    & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
      | r1_tmap_1(sK3,sK2,sK4,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_pre_topc(sK5,sK3)
    & v1_tsep_1(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f51,f57,f56,f55,f54,f53,f52])).

fof(f93,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f86,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f58])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f41])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f92,plain,(
    v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f97,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f58])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(nnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(equality_resolution,[],[f81])).

fof(f89,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f84,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f58])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(equality_resolution,[],[f80])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
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
    inference(equality_resolution,[],[f79])).

fof(f98,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_8])).

cnf(c_254,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_937,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_938,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_937])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_940,plain,
    ( v2_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_938,c_35,c_34])).

cnf(c_2123,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_254,c_940])).

cnf(c_2124,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | r2_hidden(X1,sK1(sK5,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2123])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_926,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_927,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_926])).

cnf(c_2128,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | r2_hidden(X1,sK1(sK5,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2124,c_34,c_30,c_927])).

cnf(c_8116,plain,
    ( m1_connsp_2(X0,sK5,X1) != iProver_top
    | r2_hidden(X1,sK1(sK5,X1,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2128])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_8])).

cnf(c_233,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_2186,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_940])).

cnf(c_2187,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2186])).

cnf(c_2191,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2187,c_34,c_30,c_927])).

cnf(c_8113,plain,
    ( m1_connsp_2(X0,sK5,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2191])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8153,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9606,plain,
    ( m1_connsp_2(X0,sK5,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(sK1(sK5,X1,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8113,c_8153])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_8150,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8154,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2207,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_940])).

cnf(c_2208,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ v3_pre_topc(X2,sK5)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2207])).

cnf(c_2212,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ v3_pre_topc(X2,sK5)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2208,c_34,c_30,c_927])).

cnf(c_2213,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ v3_pre_topc(X2,sK5)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X2,X0) ),
    inference(renaming,[status(thm)],[c_2212])).

cnf(c_8112,plain,
    ( m1_connsp_2(X0,sK5,X1) = iProver_top
    | v3_pre_topc(X2,sK5) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_9057,plain,
    ( m1_connsp_2(X0,sK5,X1) = iProver_top
    | v3_pre_topc(X2,sK5) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8154,c_8112])).

cnf(c_12336,plain,
    ( m1_connsp_2(X0,sK5,X1) = iProver_top
    | v3_pre_topc(X2,sK5) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8154,c_9057])).

cnf(c_13704,plain,
    ( m1_connsp_2(X0,sK5,sK7) = iProver_top
    | v3_pre_topc(X1,sK5) != iProver_top
    | r2_hidden(sK7,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8150,c_12336])).

cnf(c_13817,plain,
    ( m1_connsp_2(X0,sK5,X1) != iProver_top
    | m1_connsp_2(X2,sK5,sK7) = iProver_top
    | v3_pre_topc(sK1(sK5,X1,X0),sK5) != iProver_top
    | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X2,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(sK1(sK5,X1,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9606,c_13704])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_8])).

cnf(c_240,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_2165,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_240,c_940])).

cnf(c_2166,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | v3_pre_topc(sK1(sK5,X1,X0),sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2165])).

cnf(c_2170,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | v3_pre_topc(sK1(sK5,X1,X0),sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2166,c_34,c_30,c_927])).

cnf(c_2172,plain,
    ( m1_connsp_2(X0,sK5,X1) != iProver_top
    | v3_pre_topc(sK1(sK5,X1,X0),sK5) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2170])).

cnf(c_14489,plain,
    ( m1_connsp_2(X2,sK5,sK7) = iProver_top
    | m1_connsp_2(X0,sK5,X1) != iProver_top
    | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X2,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(sK1(sK5,X1,X0),X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13817,c_2172])).

cnf(c_14490,plain,
    ( m1_connsp_2(X0,sK5,X1) != iProver_top
    | m1_connsp_2(X2,sK5,sK7) = iProver_top
    | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X2,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(sK1(sK5,X1,X0),X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_14489])).

cnf(c_14503,plain,
    ( m1_connsp_2(X0,sK5,X1) != iProver_top
    | m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top
    | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9606,c_14490])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_11126,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_11129,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11126])).

cnf(c_18066,plain,
    ( m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
    | m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top
    | m1_connsp_2(X0,sK5,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14503,c_11129])).

cnf(c_18067,plain,
    ( m1_connsp_2(X0,sK5,X1) != iProver_top
    | m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top
    | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18066])).

cnf(c_18076,plain,
    ( m1_connsp_2(X0,sK5,sK7) != iProver_top
    | m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8116,c_18067])).

cnf(c_53,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1766,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_940])).

cnf(c_1767,plain,
    ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1766])).

cnf(c_1771,plain,
    ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1767,c_34,c_30,c_927])).

cnf(c_8604,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_8605,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8604])).

cnf(c_8620,plain,
    ( ~ m1_connsp_2(X0,sK5,sK7)
    | v3_pre_topc(sK1(sK5,sK7,X0),sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2170])).

cnf(c_8790,plain,
    ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_8620])).

cnf(c_8791,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
    | v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8790])).

cnf(c_8625,plain,
    ( ~ m1_connsp_2(X0,sK5,sK7)
    | m1_subset_1(sK1(sK5,sK7,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_8793,plain,
    ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_8625])).

cnf(c_8794,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
    | m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8793])).

cnf(c_8634,plain,
    ( ~ m1_connsp_2(X0,sK5,sK7)
    | r2_hidden(sK7,sK1(sK5,sK7,X0))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_8796,plain,
    ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_8634])).

cnf(c_8797,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
    | r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7))) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8796])).

cnf(c_9369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_9916,plain,
    ( ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_9369])).

cnf(c_9917,plain,
    ( m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9916])).

cnf(c_9903,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12402,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_9903])).

cnf(c_12403,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12402])).

cnf(c_8976,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ r2_hidden(X1,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),X0) ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_10343,plain,
    ( m1_connsp_2(X0,sK5,sK7)
    | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),X0) ),
    inference(instantiation,[status(thm)],[c_8976])).

cnf(c_20305,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK5,sK7)
    | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_10343])).

cnf(c_20307,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top
    | v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5) != iProver_top
    | r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7))) != iProver_top
    | m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20305])).

cnf(c_20452,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18076,c_53,c_8605,c_8791,c_8794,c_8797,c_9917,c_11129,c_12403,c_20307])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_8])).

cnf(c_262,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_261])).

cnf(c_2102,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_262,c_940])).

cnf(c_2103,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2102])).

cnf(c_2107,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2103,c_34,c_30,c_927])).

cnf(c_8117,plain,
    ( m1_connsp_2(X0,sK5,X1) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2107])).

cnf(c_10940,plain,
    ( m1_connsp_2(X0,sK5,sK7) != iProver_top
    | r2_hidden(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8150,c_8117])).

cnf(c_20458,plain,
    ( r2_hidden(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20452,c_10940])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_897,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_898,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_897])).

cnf(c_900,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_898,c_34])).

cnf(c_8146,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_900])).

cnf(c_1889,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_35])).

cnf(c_1890,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ v3_pre_topc(X2,sK3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1889])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1894,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ v3_pre_topc(X2,sK3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1890,c_36,c_34])).

cnf(c_8126,plain,
    ( m1_connsp_2(X0,sK3,X1) = iProver_top
    | v3_pre_topc(X2,sK3) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_10260,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,X0) = iProver_top
    | v3_pre_topc(X1,sK3) != iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8146,c_8126])).

cnf(c_11438,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,X0) = iProver_top
    | v3_pre_topc(u1_struct_0(sK5),sK3) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8146,c_10260])).

cnf(c_44,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_51,plain,
    ( m1_pre_topc(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_18,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_218,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_19])).

cnf(c_219,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_29,negated_conjecture,
    ( v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_534,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_219,c_29])).

cnf(c_535,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_536,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3) = iProver_top
    | m1_pre_topc(sK5,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_11502,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK5)) != iProver_top
    | m1_connsp_2(u1_struct_0(sK5),sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11438,c_44,c_45,c_51,c_536,c_11129])).

cnf(c_11503,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,X0) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11502])).

cnf(c_24,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_8151,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_8202,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8151,c_25])).

cnf(c_21,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_780,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_781,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_785,plain,
    ( ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_33])).

cnf(c_786,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_785])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_827,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_786,c_7])).

cnf(c_948,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_827])).

cnf(c_949,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_948])).

cnf(c_953,plain,
    ( ~ v2_pre_topc(X0)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_949,c_36,c_35,c_34,c_30])).

cnf(c_954,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_953])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1652,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_connsp_2(X2,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_954,c_38])).

cnf(c_1653,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1652])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1657,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1653,c_39,c_37,c_31])).

cnf(c_1658,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_connsp_2(X1,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1657])).

cnf(c_8138,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(sK3,sK2,sK4,X0) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0) != iProver_top
    | m1_connsp_2(X1,sK3,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1658])).

cnf(c_8437,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0) != iProver_top
    | m1_connsp_2(X1,sK3,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8138])).

cnf(c_12068,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | m1_connsp_2(X0,sK3,sK7) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8202,c_8437])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_8149,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8163,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8149,c_25])).

cnf(c_1922,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_35])).

cnf(c_1923,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1922])).

cnf(c_1927,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1923,c_36,c_34])).

cnf(c_8720,plain,
    ( ~ m1_connsp_2(X0,sK3,sK7)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_8721,plain,
    ( m1_connsp_2(X0,sK3,sK7) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8720])).

cnf(c_22,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_20,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_210,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_20])).

cnf(c_211,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_723,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_32])).

cnf(c_724,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_728,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_33])).

cnf(c_729,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_728])).

cnf(c_764,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_729,c_7])).

cnf(c_996,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_764])).

cnf(c_997,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_996])).

cnf(c_1001,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_997,c_36,c_35,c_34,c_30])).

cnf(c_1002,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_1001])).

cnf(c_1628,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1002,c_38])).

cnf(c_1629,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1628])).

cnf(c_1633,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_39,c_37,c_31])).

cnf(c_1634,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1633])).

cnf(c_8139,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(sK3,sK2,sK4,X0) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1634])).

cnf(c_8360,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8139])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_8152,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8225,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8152,c_25])).

cnf(c_11383,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8360,c_8225])).

cnf(c_12084,plain,
    ( m1_connsp_2(X0,sK3,sK7) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12068,c_53,c_8163,c_8721,c_11383])).

cnf(c_12093,plain,
    ( r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11503,c_12084])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20458,c_12093,c_11129,c_8163])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.30/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.30/1.00  
% 3.30/1.00  ------  iProver source info
% 3.30/1.00  
% 3.30/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.30/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.30/1.00  git: non_committed_changes: false
% 3.30/1.00  git: last_make_outside_of_git: false
% 3.30/1.00  
% 3.30/1.00  ------ 
% 3.30/1.00  
% 3.30/1.00  ------ Input Options
% 3.30/1.00  
% 3.30/1.00  --out_options                           all
% 3.30/1.00  --tptp_safe_out                         true
% 3.30/1.00  --problem_path                          ""
% 3.30/1.00  --include_path                          ""
% 3.30/1.00  --clausifier                            res/vclausify_rel
% 3.30/1.00  --clausifier_options                    --mode clausify
% 3.30/1.00  --stdin                                 false
% 3.30/1.00  --stats_out                             all
% 3.30/1.00  
% 3.30/1.00  ------ General Options
% 3.30/1.00  
% 3.30/1.00  --fof                                   false
% 3.30/1.00  --time_out_real                         305.
% 3.30/1.00  --time_out_virtual                      -1.
% 3.30/1.00  --symbol_type_check                     false
% 3.30/1.00  --clausify_out                          false
% 3.30/1.00  --sig_cnt_out                           false
% 3.30/1.00  --trig_cnt_out                          false
% 3.30/1.00  --trig_cnt_out_tolerance                1.
% 3.30/1.00  --trig_cnt_out_sk_spl                   false
% 3.30/1.00  --abstr_cl_out                          false
% 3.30/1.00  
% 3.30/1.00  ------ Global Options
% 3.30/1.00  
% 3.30/1.00  --schedule                              default
% 3.30/1.00  --add_important_lit                     false
% 3.30/1.00  --prop_solver_per_cl                    1000
% 3.30/1.00  --min_unsat_core                        false
% 3.30/1.00  --soft_assumptions                      false
% 3.30/1.00  --soft_lemma_size                       3
% 3.30/1.00  --prop_impl_unit_size                   0
% 3.30/1.00  --prop_impl_unit                        []
% 3.30/1.00  --share_sel_clauses                     true
% 3.30/1.00  --reset_solvers                         false
% 3.30/1.00  --bc_imp_inh                            [conj_cone]
% 3.30/1.00  --conj_cone_tolerance                   3.
% 3.30/1.00  --extra_neg_conj                        none
% 3.30/1.00  --large_theory_mode                     true
% 3.30/1.00  --prolific_symb_bound                   200
% 3.30/1.00  --lt_threshold                          2000
% 3.30/1.00  --clause_weak_htbl                      true
% 3.30/1.00  --gc_record_bc_elim                     false
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing Options
% 3.30/1.00  
% 3.30/1.00  --preprocessing_flag                    true
% 3.30/1.00  --time_out_prep_mult                    0.1
% 3.30/1.00  --splitting_mode                        input
% 3.30/1.00  --splitting_grd                         true
% 3.30/1.00  --splitting_cvd                         false
% 3.30/1.00  --splitting_cvd_svl                     false
% 3.30/1.00  --splitting_nvd                         32
% 3.30/1.00  --sub_typing                            true
% 3.30/1.00  --prep_gs_sim                           true
% 3.30/1.00  --prep_unflatten                        true
% 3.30/1.00  --prep_res_sim                          true
% 3.30/1.00  --prep_upred                            true
% 3.30/1.00  --prep_sem_filter                       exhaustive
% 3.30/1.00  --prep_sem_filter_out                   false
% 3.30/1.00  --pred_elim                             true
% 3.30/1.00  --res_sim_input                         true
% 3.30/1.00  --eq_ax_congr_red                       true
% 3.30/1.00  --pure_diseq_elim                       true
% 3.30/1.00  --brand_transform                       false
% 3.30/1.00  --non_eq_to_eq                          false
% 3.30/1.00  --prep_def_merge                        true
% 3.30/1.00  --prep_def_merge_prop_impl              false
% 3.30/1.00  --prep_def_merge_mbd                    true
% 3.30/1.00  --prep_def_merge_tr_red                 false
% 3.30/1.00  --prep_def_merge_tr_cl                  false
% 3.30/1.00  --smt_preprocessing                     true
% 3.30/1.00  --smt_ac_axioms                         fast
% 3.30/1.00  --preprocessed_out                      false
% 3.30/1.00  --preprocessed_stats                    false
% 3.30/1.00  
% 3.30/1.00  ------ Abstraction refinement Options
% 3.30/1.00  
% 3.30/1.00  --abstr_ref                             []
% 3.30/1.00  --abstr_ref_prep                        false
% 3.30/1.00  --abstr_ref_until_sat                   false
% 3.30/1.00  --abstr_ref_sig_restrict                funpre
% 3.30/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/1.00  --abstr_ref_under                       []
% 3.30/1.00  
% 3.30/1.00  ------ SAT Options
% 3.30/1.00  
% 3.30/1.00  --sat_mode                              false
% 3.30/1.00  --sat_fm_restart_options                ""
% 3.30/1.00  --sat_gr_def                            false
% 3.30/1.00  --sat_epr_types                         true
% 3.30/1.00  --sat_non_cyclic_types                  false
% 3.30/1.00  --sat_finite_models                     false
% 3.30/1.00  --sat_fm_lemmas                         false
% 3.30/1.00  --sat_fm_prep                           false
% 3.30/1.00  --sat_fm_uc_incr                        true
% 3.30/1.00  --sat_out_model                         small
% 3.30/1.00  --sat_out_clauses                       false
% 3.30/1.00  
% 3.30/1.00  ------ QBF Options
% 3.30/1.00  
% 3.30/1.00  --qbf_mode                              false
% 3.30/1.00  --qbf_elim_univ                         false
% 3.30/1.00  --qbf_dom_inst                          none
% 3.30/1.00  --qbf_dom_pre_inst                      false
% 3.30/1.00  --qbf_sk_in                             false
% 3.30/1.00  --qbf_pred_elim                         true
% 3.30/1.00  --qbf_split                             512
% 3.30/1.00  
% 3.30/1.00  ------ BMC1 Options
% 3.30/1.00  
% 3.30/1.00  --bmc1_incremental                      false
% 3.30/1.00  --bmc1_axioms                           reachable_all
% 3.30/1.00  --bmc1_min_bound                        0
% 3.30/1.00  --bmc1_max_bound                        -1
% 3.30/1.00  --bmc1_max_bound_default                -1
% 3.30/1.00  --bmc1_symbol_reachability              true
% 3.30/1.00  --bmc1_property_lemmas                  false
% 3.30/1.00  --bmc1_k_induction                      false
% 3.30/1.00  --bmc1_non_equiv_states                 false
% 3.30/1.00  --bmc1_deadlock                         false
% 3.30/1.00  --bmc1_ucm                              false
% 3.30/1.00  --bmc1_add_unsat_core                   none
% 3.30/1.00  --bmc1_unsat_core_children              false
% 3.30/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/1.00  --bmc1_out_stat                         full
% 3.30/1.00  --bmc1_ground_init                      false
% 3.30/1.00  --bmc1_pre_inst_next_state              false
% 3.30/1.00  --bmc1_pre_inst_state                   false
% 3.30/1.00  --bmc1_pre_inst_reach_state             false
% 3.30/1.00  --bmc1_out_unsat_core                   false
% 3.30/1.00  --bmc1_aig_witness_out                  false
% 3.30/1.00  --bmc1_verbose                          false
% 3.30/1.00  --bmc1_dump_clauses_tptp                false
% 3.30/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.30/1.00  --bmc1_dump_file                        -
% 3.30/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.30/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.30/1.00  --bmc1_ucm_extend_mode                  1
% 3.30/1.00  --bmc1_ucm_init_mode                    2
% 3.30/1.00  --bmc1_ucm_cone_mode                    none
% 3.30/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.30/1.00  --bmc1_ucm_relax_model                  4
% 3.30/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.30/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/1.00  --bmc1_ucm_layered_model                none
% 3.30/1.00  --bmc1_ucm_max_lemma_size               10
% 3.30/1.00  
% 3.30/1.00  ------ AIG Options
% 3.30/1.00  
% 3.30/1.00  --aig_mode                              false
% 3.30/1.00  
% 3.30/1.00  ------ Instantiation Options
% 3.30/1.00  
% 3.30/1.00  --instantiation_flag                    true
% 3.30/1.00  --inst_sos_flag                         false
% 3.30/1.00  --inst_sos_phase                        true
% 3.30/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/1.00  --inst_lit_sel_side                     num_symb
% 3.30/1.00  --inst_solver_per_active                1400
% 3.30/1.00  --inst_solver_calls_frac                1.
% 3.30/1.00  --inst_passive_queue_type               priority_queues
% 3.30/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/1.00  --inst_passive_queues_freq              [25;2]
% 3.30/1.00  --inst_dismatching                      true
% 3.30/1.00  --inst_eager_unprocessed_to_passive     true
% 3.30/1.00  --inst_prop_sim_given                   true
% 3.30/1.00  --inst_prop_sim_new                     false
% 3.30/1.00  --inst_subs_new                         false
% 3.30/1.00  --inst_eq_res_simp                      false
% 3.30/1.00  --inst_subs_given                       false
% 3.30/1.00  --inst_orphan_elimination               true
% 3.30/1.00  --inst_learning_loop_flag               true
% 3.30/1.00  --inst_learning_start                   3000
% 3.30/1.00  --inst_learning_factor                  2
% 3.30/1.00  --inst_start_prop_sim_after_learn       3
% 3.30/1.00  --inst_sel_renew                        solver
% 3.30/1.00  --inst_lit_activity_flag                true
% 3.30/1.00  --inst_restr_to_given                   false
% 3.30/1.00  --inst_activity_threshold               500
% 3.30/1.00  --inst_out_proof                        true
% 3.30/1.00  
% 3.30/1.00  ------ Resolution Options
% 3.30/1.00  
% 3.30/1.00  --resolution_flag                       true
% 3.30/1.00  --res_lit_sel                           adaptive
% 3.30/1.00  --res_lit_sel_side                      none
% 3.30/1.00  --res_ordering                          kbo
% 3.30/1.00  --res_to_prop_solver                    active
% 3.30/1.00  --res_prop_simpl_new                    false
% 3.30/1.00  --res_prop_simpl_given                  true
% 3.30/1.00  --res_passive_queue_type                priority_queues
% 3.30/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/1.00  --res_passive_queues_freq               [15;5]
% 3.30/1.00  --res_forward_subs                      full
% 3.30/1.00  --res_backward_subs                     full
% 3.30/1.00  --res_forward_subs_resolution           true
% 3.30/1.00  --res_backward_subs_resolution          true
% 3.30/1.00  --res_orphan_elimination                true
% 3.30/1.00  --res_time_limit                        2.
% 3.30/1.00  --res_out_proof                         true
% 3.30/1.00  
% 3.30/1.00  ------ Superposition Options
% 3.30/1.00  
% 3.30/1.00  --superposition_flag                    true
% 3.30/1.00  --sup_passive_queue_type                priority_queues
% 3.30/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.30/1.00  --demod_completeness_check              fast
% 3.30/1.00  --demod_use_ground                      true
% 3.30/1.00  --sup_to_prop_solver                    passive
% 3.30/1.00  --sup_prop_simpl_new                    true
% 3.30/1.00  --sup_prop_simpl_given                  true
% 3.30/1.00  --sup_fun_splitting                     false
% 3.30/1.00  --sup_smt_interval                      50000
% 3.30/1.00  
% 3.30/1.00  ------ Superposition Simplification Setup
% 3.30/1.00  
% 3.30/1.00  --sup_indices_passive                   []
% 3.30/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/1.00  --sup_full_bw                           [BwDemod]
% 3.30/1.00  --sup_immed_triv                        [TrivRules]
% 3.30/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/1.00  --sup_immed_bw_main                     []
% 3.30/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/1.00  
% 3.30/1.00  ------ Combination Options
% 3.30/1.00  
% 3.30/1.00  --comb_res_mult                         3
% 3.30/1.00  --comb_sup_mult                         2
% 3.30/1.00  --comb_inst_mult                        10
% 3.30/1.00  
% 3.30/1.00  ------ Debug Options
% 3.30/1.00  
% 3.30/1.00  --dbg_backtrace                         false
% 3.30/1.00  --dbg_dump_prop_clauses                 false
% 3.30/1.00  --dbg_dump_prop_clauses_file            -
% 3.30/1.00  --dbg_out_stat                          false
% 3.30/1.00  ------ Parsing...
% 3.30/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/1.00  ------ Proving...
% 3.30/1.00  ------ Problem Properties 
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  clauses                                 47
% 3.30/1.00  conjectures                             6
% 3.30/1.00  EPR                                     3
% 3.30/1.00  Horn                                    46
% 3.30/1.00  unary                                   7
% 3.30/1.00  binary                                  8
% 3.30/1.00  lits                                    146
% 3.30/1.00  lits eq                                 8
% 3.30/1.00  fd_pure                                 0
% 3.30/1.00  fd_pseudo                               0
% 3.30/1.00  fd_cond                                 0
% 3.30/1.00  fd_pseudo_cond                          1
% 3.30/1.00  AC symbols                              0
% 3.30/1.00  
% 3.30/1.00  ------ Schedule dynamic 5 is on 
% 3.30/1.00  
% 3.30/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  ------ 
% 3.30/1.00  Current options:
% 3.30/1.00  ------ 
% 3.30/1.00  
% 3.30/1.00  ------ Input Options
% 3.30/1.00  
% 3.30/1.00  --out_options                           all
% 3.30/1.00  --tptp_safe_out                         true
% 3.30/1.00  --problem_path                          ""
% 3.30/1.00  --include_path                          ""
% 3.30/1.00  --clausifier                            res/vclausify_rel
% 3.30/1.00  --clausifier_options                    --mode clausify
% 3.30/1.00  --stdin                                 false
% 3.30/1.00  --stats_out                             all
% 3.30/1.00  
% 3.30/1.00  ------ General Options
% 3.30/1.00  
% 3.30/1.00  --fof                                   false
% 3.30/1.00  --time_out_real                         305.
% 3.30/1.00  --time_out_virtual                      -1.
% 3.30/1.00  --symbol_type_check                     false
% 3.30/1.00  --clausify_out                          false
% 3.30/1.00  --sig_cnt_out                           false
% 3.30/1.00  --trig_cnt_out                          false
% 3.30/1.00  --trig_cnt_out_tolerance                1.
% 3.30/1.00  --trig_cnt_out_sk_spl                   false
% 3.30/1.00  --abstr_cl_out                          false
% 3.30/1.00  
% 3.30/1.00  ------ Global Options
% 3.30/1.00  
% 3.30/1.00  --schedule                              default
% 3.30/1.00  --add_important_lit                     false
% 3.30/1.00  --prop_solver_per_cl                    1000
% 3.30/1.00  --min_unsat_core                        false
% 3.30/1.00  --soft_assumptions                      false
% 3.30/1.00  --soft_lemma_size                       3
% 3.30/1.00  --prop_impl_unit_size                   0
% 3.30/1.00  --prop_impl_unit                        []
% 3.30/1.00  --share_sel_clauses                     true
% 3.30/1.00  --reset_solvers                         false
% 3.30/1.00  --bc_imp_inh                            [conj_cone]
% 3.30/1.00  --conj_cone_tolerance                   3.
% 3.30/1.00  --extra_neg_conj                        none
% 3.30/1.00  --large_theory_mode                     true
% 3.30/1.00  --prolific_symb_bound                   200
% 3.30/1.00  --lt_threshold                          2000
% 3.30/1.00  --clause_weak_htbl                      true
% 3.30/1.00  --gc_record_bc_elim                     false
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing Options
% 3.30/1.00  
% 3.30/1.00  --preprocessing_flag                    true
% 3.30/1.00  --time_out_prep_mult                    0.1
% 3.30/1.00  --splitting_mode                        input
% 3.30/1.00  --splitting_grd                         true
% 3.30/1.00  --splitting_cvd                         false
% 3.30/1.00  --splitting_cvd_svl                     false
% 3.30/1.00  --splitting_nvd                         32
% 3.30/1.00  --sub_typing                            true
% 3.30/1.00  --prep_gs_sim                           true
% 3.30/1.00  --prep_unflatten                        true
% 3.30/1.00  --prep_res_sim                          true
% 3.30/1.00  --prep_upred                            true
% 3.30/1.00  --prep_sem_filter                       exhaustive
% 3.30/1.00  --prep_sem_filter_out                   false
% 3.30/1.00  --pred_elim                             true
% 3.30/1.00  --res_sim_input                         true
% 3.30/1.00  --eq_ax_congr_red                       true
% 3.30/1.00  --pure_diseq_elim                       true
% 3.30/1.00  --brand_transform                       false
% 3.30/1.00  --non_eq_to_eq                          false
% 3.30/1.00  --prep_def_merge                        true
% 3.30/1.00  --prep_def_merge_prop_impl              false
% 3.30/1.00  --prep_def_merge_mbd                    true
% 3.30/1.00  --prep_def_merge_tr_red                 false
% 3.30/1.00  --prep_def_merge_tr_cl                  false
% 3.30/1.00  --smt_preprocessing                     true
% 3.30/1.00  --smt_ac_axioms                         fast
% 3.30/1.00  --preprocessed_out                      false
% 3.30/1.00  --preprocessed_stats                    false
% 3.30/1.00  
% 3.30/1.00  ------ Abstraction refinement Options
% 3.30/1.00  
% 3.30/1.00  --abstr_ref                             []
% 3.30/1.00  --abstr_ref_prep                        false
% 3.30/1.00  --abstr_ref_until_sat                   false
% 3.30/1.00  --abstr_ref_sig_restrict                funpre
% 3.30/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/1.00  --abstr_ref_under                       []
% 3.30/1.00  
% 3.30/1.00  ------ SAT Options
% 3.30/1.00  
% 3.30/1.00  --sat_mode                              false
% 3.30/1.00  --sat_fm_restart_options                ""
% 3.30/1.00  --sat_gr_def                            false
% 3.30/1.00  --sat_epr_types                         true
% 3.30/1.00  --sat_non_cyclic_types                  false
% 3.30/1.00  --sat_finite_models                     false
% 3.30/1.00  --sat_fm_lemmas                         false
% 3.30/1.00  --sat_fm_prep                           false
% 3.30/1.00  --sat_fm_uc_incr                        true
% 3.30/1.00  --sat_out_model                         small
% 3.30/1.00  --sat_out_clauses                       false
% 3.30/1.00  
% 3.30/1.00  ------ QBF Options
% 3.30/1.00  
% 3.30/1.00  --qbf_mode                              false
% 3.30/1.00  --qbf_elim_univ                         false
% 3.30/1.00  --qbf_dom_inst                          none
% 3.30/1.00  --qbf_dom_pre_inst                      false
% 3.30/1.00  --qbf_sk_in                             false
% 3.30/1.00  --qbf_pred_elim                         true
% 3.30/1.00  --qbf_split                             512
% 3.30/1.00  
% 3.30/1.00  ------ BMC1 Options
% 3.30/1.00  
% 3.30/1.00  --bmc1_incremental                      false
% 3.30/1.00  --bmc1_axioms                           reachable_all
% 3.30/1.00  --bmc1_min_bound                        0
% 3.30/1.00  --bmc1_max_bound                        -1
% 3.30/1.00  --bmc1_max_bound_default                -1
% 3.30/1.00  --bmc1_symbol_reachability              true
% 3.30/1.00  --bmc1_property_lemmas                  false
% 3.30/1.00  --bmc1_k_induction                      false
% 3.30/1.00  --bmc1_non_equiv_states                 false
% 3.30/1.00  --bmc1_deadlock                         false
% 3.30/1.00  --bmc1_ucm                              false
% 3.30/1.00  --bmc1_add_unsat_core                   none
% 3.30/1.00  --bmc1_unsat_core_children              false
% 3.30/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/1.00  --bmc1_out_stat                         full
% 3.30/1.00  --bmc1_ground_init                      false
% 3.30/1.00  --bmc1_pre_inst_next_state              false
% 3.30/1.00  --bmc1_pre_inst_state                   false
% 3.30/1.00  --bmc1_pre_inst_reach_state             false
% 3.30/1.00  --bmc1_out_unsat_core                   false
% 3.30/1.00  --bmc1_aig_witness_out                  false
% 3.30/1.00  --bmc1_verbose                          false
% 3.30/1.00  --bmc1_dump_clauses_tptp                false
% 3.30/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.30/1.00  --bmc1_dump_file                        -
% 3.30/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.30/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.30/1.00  --bmc1_ucm_extend_mode                  1
% 3.30/1.00  --bmc1_ucm_init_mode                    2
% 3.30/1.00  --bmc1_ucm_cone_mode                    none
% 3.30/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.30/1.00  --bmc1_ucm_relax_model                  4
% 3.30/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.30/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/1.00  --bmc1_ucm_layered_model                none
% 3.30/1.00  --bmc1_ucm_max_lemma_size               10
% 3.30/1.00  
% 3.30/1.00  ------ AIG Options
% 3.30/1.00  
% 3.30/1.00  --aig_mode                              false
% 3.30/1.00  
% 3.30/1.00  ------ Instantiation Options
% 3.30/1.00  
% 3.30/1.00  --instantiation_flag                    true
% 3.30/1.00  --inst_sos_flag                         false
% 3.30/1.00  --inst_sos_phase                        true
% 3.30/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/1.00  --inst_lit_sel_side                     none
% 3.30/1.00  --inst_solver_per_active                1400
% 3.30/1.00  --inst_solver_calls_frac                1.
% 3.30/1.00  --inst_passive_queue_type               priority_queues
% 3.30/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/1.00  --inst_passive_queues_freq              [25;2]
% 3.30/1.00  --inst_dismatching                      true
% 3.30/1.00  --inst_eager_unprocessed_to_passive     true
% 3.30/1.00  --inst_prop_sim_given                   true
% 3.30/1.00  --inst_prop_sim_new                     false
% 3.30/1.00  --inst_subs_new                         false
% 3.30/1.00  --inst_eq_res_simp                      false
% 3.30/1.00  --inst_subs_given                       false
% 3.30/1.00  --inst_orphan_elimination               true
% 3.30/1.00  --inst_learning_loop_flag               true
% 3.30/1.00  --inst_learning_start                   3000
% 3.30/1.00  --inst_learning_factor                  2
% 3.30/1.00  --inst_start_prop_sim_after_learn       3
% 3.30/1.00  --inst_sel_renew                        solver
% 3.30/1.00  --inst_lit_activity_flag                true
% 3.30/1.00  --inst_restr_to_given                   false
% 3.30/1.00  --inst_activity_threshold               500
% 3.30/1.00  --inst_out_proof                        true
% 3.30/1.00  
% 3.30/1.00  ------ Resolution Options
% 3.30/1.00  
% 3.30/1.00  --resolution_flag                       false
% 3.30/1.00  --res_lit_sel                           adaptive
% 3.30/1.00  --res_lit_sel_side                      none
% 3.30/1.00  --res_ordering                          kbo
% 3.30/1.00  --res_to_prop_solver                    active
% 3.30/1.00  --res_prop_simpl_new                    false
% 3.30/1.00  --res_prop_simpl_given                  true
% 3.30/1.00  --res_passive_queue_type                priority_queues
% 3.30/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/1.00  --res_passive_queues_freq               [15;5]
% 3.30/1.00  --res_forward_subs                      full
% 3.30/1.00  --res_backward_subs                     full
% 3.30/1.00  --res_forward_subs_resolution           true
% 3.30/1.00  --res_backward_subs_resolution          true
% 3.30/1.00  --res_orphan_elimination                true
% 3.30/1.00  --res_time_limit                        2.
% 3.30/1.00  --res_out_proof                         true
% 3.30/1.00  
% 3.30/1.00  ------ Superposition Options
% 3.30/1.00  
% 3.30/1.00  --superposition_flag                    true
% 3.30/1.00  --sup_passive_queue_type                priority_queues
% 3.30/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.30/1.00  --demod_completeness_check              fast
% 3.30/1.00  --demod_use_ground                      true
% 3.30/1.00  --sup_to_prop_solver                    passive
% 3.30/1.00  --sup_prop_simpl_new                    true
% 3.30/1.00  --sup_prop_simpl_given                  true
% 3.30/1.00  --sup_fun_splitting                     false
% 3.30/1.00  --sup_smt_interval                      50000
% 3.30/1.00  
% 3.30/1.00  ------ Superposition Simplification Setup
% 3.30/1.00  
% 3.30/1.00  --sup_indices_passive                   []
% 3.30/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/1.00  --sup_full_bw                           [BwDemod]
% 3.30/1.00  --sup_immed_triv                        [TrivRules]
% 3.30/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/1.00  --sup_immed_bw_main                     []
% 3.30/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/1.00  
% 3.30/1.00  ------ Combination Options
% 3.30/1.00  
% 3.30/1.00  --comb_res_mult                         3
% 3.30/1.00  --comb_sup_mult                         2
% 3.30/1.00  --comb_inst_mult                        10
% 3.30/1.00  
% 3.30/1.00  ------ Debug Options
% 3.30/1.00  
% 3.30/1.00  --dbg_backtrace                         false
% 3.30/1.00  --dbg_dump_prop_clauses                 false
% 3.30/1.00  --dbg_dump_prop_clauses_file            -
% 3.30/1.00  --dbg_out_stat                          false
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  ------ Proving...
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  % SZS status Theorem for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  fof(f9,axiom,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f27,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f9])).
% 3.30/1.00  
% 3.30/1.00  fof(f28,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f27])).
% 3.30/1.00  
% 3.30/1.00  fof(f43,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(nnf_transformation,[],[f28])).
% 3.30/1.00  
% 3.30/1.00  fof(f44,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(rectify,[],[f43])).
% 3.30/1.00  
% 3.30/1.00  fof(f45,plain,(
% 3.30/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f46,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 3.30/1.00  
% 3.30/1.00  fof(f73,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f46])).
% 3.30/1.00  
% 3.30/1.00  fof(f6,axiom,(
% 3.30/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f21,plain,(
% 3.30/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f6])).
% 3.30/1.00  
% 3.30/1.00  fof(f22,plain,(
% 3.30/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f21])).
% 3.30/1.00  
% 3.30/1.00  fof(f67,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f22])).
% 3.30/1.00  
% 3.30/1.00  fof(f3,axiom,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f16,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f3])).
% 3.30/1.00  
% 3.30/1.00  fof(f17,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/1.00    inference(flattening,[],[f16])).
% 3.30/1.00  
% 3.30/1.00  fof(f64,plain,(
% 3.30/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f17])).
% 3.30/1.00  
% 3.30/1.00  fof(f14,conjecture,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f15,negated_conjecture,(
% 3.30/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.30/1.00    inference(negated_conjecture,[],[f14])).
% 3.30/1.00  
% 3.30/1.00  fof(f36,plain,(
% 3.30/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f15])).
% 3.30/1.00  
% 3.30/1.00  fof(f37,plain,(
% 3.30/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f36])).
% 3.30/1.00  
% 3.30/1.00  fof(f50,plain,(
% 3.30/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.30/1.00    inference(nnf_transformation,[],[f37])).
% 3.30/1.00  
% 3.30/1.00  fof(f51,plain,(
% 3.30/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f50])).
% 3.30/1.00  
% 3.30/1.00  fof(f57,plain,(
% 3.30/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | r1_tmap_1(X1,X0,X2,X4)) & sK7 = X4 & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f56,plain,(
% 3.30/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK6)) & sK6 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f55,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK5,X1) & v1_tsep_1(sK5,X1) & ~v2_struct_0(sK5))) )),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f54,plain,(
% 3.30/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | ~r1_tmap_1(X1,X0,sK4,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | r1_tmap_1(X1,X0,sK4,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f53,plain,(
% 3.30/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | ~r1_tmap_1(sK3,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | r1_tmap_1(sK3,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(X3,sK3) & v1_tsep_1(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f52,plain,(
% 3.30/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | ~r1_tmap_1(X1,sK2,X2,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | r1_tmap_1(X1,sK2,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f58,plain,(
% 3.30/1.00    ((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_pre_topc(sK5,sK3) & v1_tsep_1(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f51,f57,f56,f55,f54,f53,f52])).
% 3.30/1.00  
% 3.30/1.00  fof(f93,plain,(
% 3.30/1.00    m1_pre_topc(sK5,sK3)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f86,plain,(
% 3.30/1.00    v2_pre_topc(sK3)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f87,plain,(
% 3.30/1.00    l1_pre_topc(sK3)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f91,plain,(
% 3.30/1.00    ~v2_struct_0(sK5)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f4,axiom,(
% 3.30/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f18,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.30/1.00    inference(ennf_transformation,[],[f4])).
% 3.30/1.00  
% 3.30/1.00  fof(f65,plain,(
% 3.30/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f18])).
% 3.30/1.00  
% 3.30/1.00  fof(f70,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f46])).
% 3.30/1.00  
% 3.30/1.00  fof(f2,axiom,(
% 3.30/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f40,plain,(
% 3.30/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.30/1.00    inference(nnf_transformation,[],[f2])).
% 3.30/1.00  
% 3.30/1.00  fof(f62,plain,(
% 3.30/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f40])).
% 3.30/1.00  
% 3.30/1.00  fof(f95,plain,(
% 3.30/1.00    m1_subset_1(sK7,u1_struct_0(sK5))),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f63,plain,(
% 3.30/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f40])).
% 3.30/1.00  
% 3.30/1.00  fof(f74,plain,(
% 3.30/1.00    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f46])).
% 3.30/1.00  
% 3.30/1.00  fof(f71,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f46])).
% 3.30/1.00  
% 3.30/1.00  fof(f1,axiom,(
% 3.30/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f38,plain,(
% 3.30/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.30/1.00    inference(nnf_transformation,[],[f1])).
% 3.30/1.00  
% 3.30/1.00  fof(f39,plain,(
% 3.30/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.30/1.00    inference(flattening,[],[f38])).
% 3.30/1.00  
% 3.30/1.00  fof(f60,plain,(
% 3.30/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.30/1.00    inference(cnf_transformation,[],[f39])).
% 3.30/1.00  
% 3.30/1.00  fof(f99,plain,(
% 3.30/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.30/1.00    inference(equality_resolution,[],[f60])).
% 3.30/1.00  
% 3.30/1.00  fof(f7,axiom,(
% 3.30/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f23,plain,(
% 3.30/1.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f7])).
% 3.30/1.00  
% 3.30/1.00  fof(f24,plain,(
% 3.30/1.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f23])).
% 3.30/1.00  
% 3.30/1.00  fof(f41,plain,(
% 3.30/1.00    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f42,plain,(
% 3.30/1.00    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f41])).
% 3.30/1.00  
% 3.30/1.00  fof(f68,plain,(
% 3.30/1.00    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f42])).
% 3.30/1.00  
% 3.30/1.00  fof(f8,axiom,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f25,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f8])).
% 3.30/1.00  
% 3.30/1.00  fof(f26,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f25])).
% 3.30/1.00  
% 3.30/1.00  fof(f69,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f26])).
% 3.30/1.00  
% 3.30/1.00  fof(f11,axiom,(
% 3.30/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f31,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.30/1.00    inference(ennf_transformation,[],[f11])).
% 3.30/1.00  
% 3.30/1.00  fof(f78,plain,(
% 3.30/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f31])).
% 3.30/1.00  
% 3.30/1.00  fof(f85,plain,(
% 3.30/1.00    ~v2_struct_0(sK3)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f10,axiom,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f29,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f10])).
% 3.30/1.00  
% 3.30/1.00  fof(f30,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/1.00    inference(flattening,[],[f29])).
% 3.30/1.00  
% 3.30/1.00  fof(f47,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/1.00    inference(nnf_transformation,[],[f30])).
% 3.30/1.00  
% 3.30/1.00  fof(f48,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/1.00    inference(flattening,[],[f47])).
% 3.30/1.00  
% 3.30/1.00  fof(f75,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f48])).
% 3.30/1.00  
% 3.30/1.00  fof(f103,plain,(
% 3.30/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.30/1.00    inference(equality_resolution,[],[f75])).
% 3.30/1.00  
% 3.30/1.00  fof(f92,plain,(
% 3.30/1.00    v1_tsep_1(sK5,sK3)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f97,plain,(
% 3.30/1.00    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f96,plain,(
% 3.30/1.00    sK6 = sK7),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f13,axiom,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f34,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f13])).
% 3.30/1.00  
% 3.30/1.00  fof(f35,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f34])).
% 3.30/1.00  
% 3.30/1.00  fof(f49,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(nnf_transformation,[],[f35])).
% 3.30/1.00  
% 3.30/1.00  fof(f81,plain,(
% 3.30/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f49])).
% 3.30/1.00  
% 3.30/1.00  fof(f105,plain,(
% 3.30/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(equality_resolution,[],[f81])).
% 3.30/1.00  
% 3.30/1.00  fof(f89,plain,(
% 3.30/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f88,plain,(
% 3.30/1.00    v1_funct_1(sK4)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f5,axiom,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f19,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f5])).
% 3.30/1.00  
% 3.30/1.00  fof(f20,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f19])).
% 3.30/1.00  
% 3.30/1.00  fof(f66,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f20])).
% 3.30/1.00  
% 3.30/1.00  fof(f83,plain,(
% 3.30/1.00    v2_pre_topc(sK2)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f82,plain,(
% 3.30/1.00    ~v2_struct_0(sK2)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f84,plain,(
% 3.30/1.00    l1_pre_topc(sK2)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f90,plain,(
% 3.30/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f94,plain,(
% 3.30/1.00    m1_subset_1(sK6,u1_struct_0(sK3))),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  fof(f80,plain,(
% 3.30/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f49])).
% 3.30/1.00  
% 3.30/1.00  fof(f106,plain,(
% 3.30/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(equality_resolution,[],[f80])).
% 3.30/1.00  
% 3.30/1.00  fof(f12,axiom,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 3.30/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f32,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f12])).
% 3.30/1.00  
% 3.30/1.00  fof(f33,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f32])).
% 3.30/1.00  
% 3.30/1.00  fof(f79,plain,(
% 3.30/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f33])).
% 3.30/1.00  
% 3.30/1.00  fof(f104,plain,(
% 3.30/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(equality_resolution,[],[f79])).
% 3.30/1.00  
% 3.30/1.00  fof(f98,plain,(
% 3.30/1.00    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)),
% 3.30/1.00    inference(cnf_transformation,[],[f58])).
% 3.30/1.00  
% 3.30/1.00  cnf(c_12,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | r2_hidden(X2,sK1(X1,X2,X0))
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_253,plain,
% 3.30/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | r2_hidden(X2,sK1(X1,X2,X0))
% 3.30/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_12,c_8]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_254,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | r2_hidden(X2,sK1(X1,X2,X0))
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_253]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_5,plain,
% 3.30/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | v2_pre_topc(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_28,negated_conjecture,
% 3.30/1.00      ( m1_pre_topc(sK5,sK3) ),
% 3.30/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_937,plain,
% 3.30/1.00      ( ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X0)
% 3.30/1.00      | v2_pre_topc(X1)
% 3.30/1.00      | sK3 != X0
% 3.30/1.00      | sK5 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_28]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_938,plain,
% 3.30/1.00      ( ~ l1_pre_topc(sK3) | ~ v2_pre_topc(sK3) | v2_pre_topc(sK5) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_937]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_35,negated_conjecture,
% 3.30/1.00      ( v2_pre_topc(sK3) ),
% 3.30/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_34,negated_conjecture,
% 3.30/1.00      ( l1_pre_topc(sK3) ),
% 3.30/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_940,plain,
% 3.30/1.00      ( v2_pre_topc(sK5) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_938,c_35,c_34]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2123,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | r2_hidden(X2,sK1(X1,X2,X0))
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | sK5 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_254,c_940]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2124,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | r2_hidden(X1,sK1(sK5,X1,X0))
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | v2_struct_0(sK5)
% 3.30/1.00      | ~ l1_pre_topc(sK5) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_2123]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_30,negated_conjecture,
% 3.30/1.00      ( ~ v2_struct_0(sK5) ),
% 3.30/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6,plain,
% 3.30/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_926,plain,
% 3.30/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X0 | sK5 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_28]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_927,plain,
% 3.30/1.00      ( ~ l1_pre_topc(sK3) | l1_pre_topc(sK5) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_926]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2128,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | r2_hidden(X1,sK1(sK5,X1,X0))
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_2124,c_34,c_30,c_927]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8116,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) != iProver_top
% 3.30/1.00      | r2_hidden(X1,sK1(sK5,X1,X0)) = iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_2128]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_15,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_232,plain,
% 3.30/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_15,c_8]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_233,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_232]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2186,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | sK5 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_233,c_940]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2187,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | v2_struct_0(sK5)
% 3.30/1.00      | ~ l1_pre_topc(sK5) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_2186]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2191,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_2187,c_34,c_30,c_927]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8113,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_2191]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8153,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.30/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9606,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(sK1(sK5,X1,X0),u1_struct_0(sK5)) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8113,c_8153]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_26,negated_conjecture,
% 3.30/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8150,plain,
% 3.30/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8154,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.30/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_11,plain,
% 3.30/1.00      ( m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | ~ v3_pre_topc(X3,X1)
% 3.30/1.00      | ~ r2_hidden(X2,X3)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ r1_tarski(X3,X0)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2207,plain,
% 3.30/1.00      ( m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | ~ v3_pre_topc(X3,X1)
% 3.30/1.00      | ~ r2_hidden(X2,X3)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ r1_tarski(X3,X0)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | sK5 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_940]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2208,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | ~ v3_pre_topc(X2,sK5)
% 3.30/1.00      | ~ r2_hidden(X1,X2)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ r1_tarski(X2,X0)
% 3.30/1.00      | v2_struct_0(sK5)
% 3.30/1.00      | ~ l1_pre_topc(sK5) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_2207]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2212,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | ~ v3_pre_topc(X2,sK5)
% 3.30/1.00      | ~ r2_hidden(X1,X2)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ r1_tarski(X2,X0) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_2208,c_34,c_30,c_927]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2213,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | ~ v3_pre_topc(X2,sK5)
% 3.30/1.00      | ~ r2_hidden(X1,X2)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ r1_tarski(X2,X0) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_2212]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8112,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) = iProver_top
% 3.30/1.00      | v3_pre_topc(X2,sK5) != iProver_top
% 3.30/1.00      | r2_hidden(X1,X2) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.30/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9057,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) = iProver_top
% 3.30/1.00      | v3_pre_topc(X2,sK5) != iProver_top
% 3.30/1.00      | r2_hidden(X1,X2) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.30/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.30/1.00      | r1_tarski(X2,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8154,c_8112]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_12336,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) = iProver_top
% 3.30/1.00      | v3_pre_topc(X2,sK5) != iProver_top
% 3.30/1.00      | r2_hidden(X1,X2) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.30/1.00      | r1_tarski(X2,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8154,c_9057]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_13704,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,sK7) = iProver_top
% 3.30/1.00      | v3_pre_topc(X1,sK5) != iProver_top
% 3.30/1.00      | r2_hidden(sK7,X1) != iProver_top
% 3.30/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.30/1.00      | r1_tarski(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8150,c_12336]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_13817,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) != iProver_top
% 3.30/1.00      | m1_connsp_2(X2,sK5,sK7) = iProver_top
% 3.30/1.00      | v3_pre_topc(sK1(sK5,X1,X0),sK5) != iProver_top
% 3.30/1.00      | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(X2,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(sK1(sK5,X1,X0),X2) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_9606,c_13704]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_14,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_239,plain,
% 3.30/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 3.30/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_14,c_8]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_240,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_239]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2165,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | sK5 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_240,c_940]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2166,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | v3_pre_topc(sK1(sK5,X1,X0),sK5)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | v2_struct_0(sK5)
% 3.30/1.00      | ~ l1_pre_topc(sK5) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_2165]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2170,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | v3_pre_topc(sK1(sK5,X1,X0),sK5)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_2166,c_34,c_30,c_927]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2172,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) != iProver_top
% 3.30/1.00      | v3_pre_topc(sK1(sK5,X1,X0),sK5) = iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_2170]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_14489,plain,
% 3.30/1.00      ( m1_connsp_2(X2,sK5,sK7) = iProver_top
% 3.30/1.00      | m1_connsp_2(X0,sK5,X1) != iProver_top
% 3.30/1.00      | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(X2,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(sK1(sK5,X1,X0),X2) != iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_13817,c_2172]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_14490,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) != iProver_top
% 3.30/1.00      | m1_connsp_2(X2,sK5,sK7) = iProver_top
% 3.30/1.00      | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(X2,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(sK1(sK5,X1,X0),X2) != iProver_top ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_14489]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_14503,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) != iProver_top
% 3.30/1.00      | m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top
% 3.30/1.00      | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_9606,c_14490]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1,plain,
% 3.30/1.00      ( r1_tarski(X0,X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_11126,plain,
% 3.30/1.00      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_11129,plain,
% 3.30/1.00      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_11126]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_18066,plain,
% 3.30/1.00      ( m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
% 3.30/1.00      | m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top
% 3.30/1.00      | m1_connsp_2(X0,sK5,X1) != iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_14503,c_11129]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_18067,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) != iProver_top
% 3.30/1.00      | m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top
% 3.30/1.00      | r2_hidden(sK7,sK1(sK5,X1,X0)) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_18066]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_18076,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,sK7) != iProver_top
% 3.30/1.00      | m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top
% 3.30/1.00      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8116,c_18067]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_53,plain,
% 3.30/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9,plain,
% 3.30/1.00      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1766,plain,
% 3.30/1.00      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | sK5 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_940]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1767,plain,
% 3.30/1.00      ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
% 3.30/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.30/1.00      | v2_struct_0(sK5)
% 3.30/1.00      | ~ l1_pre_topc(sK5) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_1766]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1771,plain,
% 3.30/1.00      ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
% 3.30/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_1767,c_34,c_30,c_927]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8604,plain,
% 3.30/1.00      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 3.30/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1771]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8605,plain,
% 3.30/1.00      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) = iProver_top
% 3.30/1.00      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_8604]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8620,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,sK7)
% 3.30/1.00      | v3_pre_topc(sK1(sK5,sK7,X0),sK5)
% 3.30/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_2170]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8790,plain,
% 3.30/1.00      ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 3.30/1.00      | v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 3.30/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_8620]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8791,plain,
% 3.30/1.00      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
% 3.30/1.00      | v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5) = iProver_top
% 3.30/1.00      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_8790]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8625,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,sK7)
% 3.30/1.00      | m1_subset_1(sK1(sK5,sK7,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_2191]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8793,plain,
% 3.30/1.00      ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 3.30/1.00      | m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_8625]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8794,plain,
% 3.30/1.00      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
% 3.30/1.00      | m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.30/1.00      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_8793]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8634,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,sK7)
% 3.30/1.00      | r2_hidden(sK7,sK1(sK5,sK7,X0))
% 3.30/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_2128]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8796,plain,
% 3.30/1.00      ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 3.30/1.00      | r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
% 3.30/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_8634]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8797,plain,
% 3.30/1.00      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
% 3.30/1.00      | r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7))) = iProver_top
% 3.30/1.00      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_8796]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9369,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | r1_tarski(X0,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9916,plain,
% 3.30/1.00      ( ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_9369]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9917,plain,
% 3.30/1.00      ( m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.30/1.00      | r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5)) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_9916]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9903,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_12402,plain,
% 3.30/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_9903]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_12403,plain,
% 3.30/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.30/1.00      | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_12402]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8976,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 3.30/1.00      | ~ r2_hidden(X1,sK1(sK5,sK7,sK0(sK5,sK7)))
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),X0) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_2213]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_10343,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,sK7)
% 3.30/1.00      | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 3.30/1.00      | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 3.30/1.00      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),X0) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_8976]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_20305,plain,
% 3.30/1.00      ( m1_connsp_2(u1_struct_0(sK5),sK5,sK7)
% 3.30/1.00      | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 3.30/1.00      | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
% 3.30/1.00      | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.30/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 3.30/1.00      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_10343]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_20307,plain,
% 3.30/1.00      ( m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top
% 3.30/1.00      | v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5) != iProver_top
% 3.30/1.00      | r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7))) != iProver_top
% 3.30/1.00      | m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.30/1.00      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.30/1.00      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_20305]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_20452,plain,
% 3.30/1.00      ( m1_connsp_2(u1_struct_0(sK5),sK5,sK7) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_18076,c_53,c_8605,c_8791,c_8794,c_8797,c_9917,c_11129,
% 3.30/1.00                 c_12403,c_20307]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_10,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | r2_hidden(X2,X0)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_261,plain,
% 3.30/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | r2_hidden(X2,X0)
% 3.30/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_10,c_8]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_262,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | r2_hidden(X2,X0)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_261]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2102,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | r2_hidden(X2,X0)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | sK5 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_262,c_940]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2103,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | r2_hidden(X1,X0)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | v2_struct_0(sK5)
% 3.30/1.00      | ~ l1_pre_topc(sK5) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_2102]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2107,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.30/1.00      | r2_hidden(X1,X0)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_2103,c_34,c_30,c_927]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8117,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,X1) != iProver_top
% 3.30/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_2107]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_10940,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK5,sK7) != iProver_top
% 3.30/1.00      | r2_hidden(sK7,X0) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8150,c_8117]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_20458,plain,
% 3.30/1.00      ( r2_hidden(sK7,u1_struct_0(sK5)) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_20452,c_10940]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_19,plain,
% 3.30/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.30/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ l1_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_897,plain,
% 3.30/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | sK3 != X1
% 3.30/1.00      | sK5 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_898,plain,
% 3.30/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ l1_pre_topc(sK3) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_897]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_900,plain,
% 3.30/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_898,c_34]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8146,plain,
% 3.30/1.00      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_900]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1889,plain,
% 3.30/1.00      ( m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | ~ v3_pre_topc(X3,X1)
% 3.30/1.00      | ~ r2_hidden(X2,X3)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ r1_tarski(X3,X0)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | sK3 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_35]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1890,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK3,X1)
% 3.30/1.00      | ~ v3_pre_topc(X2,sK3)
% 3.30/1.00      | ~ r2_hidden(X1,X2)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ r1_tarski(X2,X0)
% 3.30/1.00      | v2_struct_0(sK3)
% 3.30/1.00      | ~ l1_pre_topc(sK3) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_1889]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_36,negated_conjecture,
% 3.30/1.00      ( ~ v2_struct_0(sK3) ),
% 3.30/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1894,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK3,X1)
% 3.30/1.00      | ~ v3_pre_topc(X2,sK3)
% 3.30/1.00      | ~ r2_hidden(X1,X2)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ r1_tarski(X2,X0) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_1890,c_36,c_34]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8126,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK3,X1) = iProver_top
% 3.30/1.00      | v3_pre_topc(X2,sK3) != iProver_top
% 3.30/1.00      | r2_hidden(X1,X2) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_10260,plain,
% 3.30/1.00      ( m1_connsp_2(u1_struct_0(sK5),sK3,X0) = iProver_top
% 3.30/1.00      | v3_pre_topc(X1,sK3) != iProver_top
% 3.30/1.00      | r2_hidden(X0,X1) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/1.00      | r1_tarski(X1,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8146,c_8126]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_11438,plain,
% 3.30/1.00      ( m1_connsp_2(u1_struct_0(sK5),sK3,X0) = iProver_top
% 3.30/1.00      | v3_pre_topc(u1_struct_0(sK5),sK3) != iProver_top
% 3.30/1.00      | r2_hidden(X0,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.30/1.00      | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8146,c_10260]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_44,plain,
% 3.30/1.00      ( v2_pre_topc(sK3) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_45,plain,
% 3.30/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_51,plain,
% 3.30/1.00      ( m1_pre_topc(sK5,sK3) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_18,plain,
% 3.30/1.00      ( ~ v1_tsep_1(X0,X1)
% 3.30/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.30/1.00      | ~ m1_pre_topc(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_218,plain,
% 3.30/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.30/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.30/1.00      | ~ v1_tsep_1(X0,X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_18,c_19]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_219,plain,
% 3.30/1.00      ( ~ v1_tsep_1(X0,X1)
% 3.30/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.30/1.00      | ~ m1_pre_topc(X0,X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_218]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_29,negated_conjecture,
% 3.30/1.00      ( v1_tsep_1(sK5,sK3) ),
% 3.30/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_534,plain,
% 3.30/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.30/1.00      | ~ m1_pre_topc(X0,X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | sK3 != X1
% 3.30/1.00      | sK5 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_219,c_29]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_535,plain,
% 3.30/1.00      ( v3_pre_topc(u1_struct_0(sK5),sK3)
% 3.30/1.00      | ~ m1_pre_topc(sK5,sK3)
% 3.30/1.00      | ~ l1_pre_topc(sK3)
% 3.30/1.00      | ~ v2_pre_topc(sK3) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_534]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_536,plain,
% 3.30/1.00      ( v3_pre_topc(u1_struct_0(sK5),sK3) = iProver_top
% 3.30/1.00      | m1_pre_topc(sK5,sK3) != iProver_top
% 3.30/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.30/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_11502,plain,
% 3.30/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.30/1.00      | r2_hidden(X0,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | m1_connsp_2(u1_struct_0(sK5),sK3,X0) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_11438,c_44,c_45,c_51,c_536,c_11129]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_11503,plain,
% 3.30/1.00      ( m1_connsp_2(u1_struct_0(sK5),sK3,X0) = iProver_top
% 3.30/1.00      | r2_hidden(X0,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_11502]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_24,negated_conjecture,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 3.30/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8151,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_25,negated_conjecture,
% 3.30/1.00      ( sK6 = sK7 ),
% 3.30/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8202,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 3.30/1.00      inference(light_normalisation,[status(thm)],[c_8151,c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_21,plain,
% 3.30/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.30/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.30/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.30/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 3.30/1.00      | ~ m1_pre_topc(X4,X0)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.30/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.30/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.30/1.00      | ~ v1_funct_1(X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X4)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_32,negated_conjecture,
% 3.30/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_780,plain,
% 3.30/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.30/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.30/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 3.30/1.00      | ~ m1_pre_topc(X4,X0)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.30/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.30/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.30/1.00      | ~ v1_funct_1(X2)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X4)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.30/1.00      | sK4 != X2 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_781,plain,
% 3.30/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.30/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 3.30/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.30/1.00      | ~ m1_pre_topc(X0,X2)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.30/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.30/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.30/1.00      | ~ v1_funct_1(sK4)
% 3.30/1.00      | v2_struct_0(X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X2)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X2)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_780]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_33,negated_conjecture,
% 3.30/1.00      ( v1_funct_1(sK4) ),
% 3.30/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_785,plain,
% 3.30/1.00      ( ~ r1_tarski(X4,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.30/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_pre_topc(X0,X2)
% 3.30/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.30/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 3.30/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.30/1.00      | v2_struct_0(X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X2)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X2)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_781,c_33]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_786,plain,
% 3.30/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.30/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 3.30/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.30/1.00      | ~ m1_pre_topc(X0,X2)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.30/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.30/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X2)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ l1_pre_topc(X2)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X2)
% 3.30/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_785]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_7,plain,
% 3.30/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.30/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_827,plain,
% 3.30/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.30/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 3.30/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.30/1.00      | ~ m1_pre_topc(X0,X2)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.30/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X2)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ l1_pre_topc(X2)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X2)
% 3.30/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_786,c_7]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_948,plain,
% 3.30/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.30/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 3.30/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.30/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X2)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X2)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.30/1.00      | sK3 != X2
% 3.30/1.00      | sK5 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_827]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_949,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,X0,sK4,X1)
% 3.30/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.30/1.00      | ~ m1_connsp_2(X2,sK3,X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.30/1.00      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(sK3)
% 3.30/1.00      | v2_struct_0(sK5)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ l1_pre_topc(sK3)
% 3.30/1.00      | ~ v2_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(sK3)
% 3.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_948]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_953,plain,
% 3.30/1.00      ( ~ v2_pre_topc(X0)
% 3.30/1.00      | r1_tmap_1(sK3,X0,sK4,X1)
% 3.30/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.30/1.00      | ~ m1_connsp_2(X2,sK3,X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.30/1.00      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_949,c_36,c_35,c_34,c_30]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_954,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,X0,sK4,X1)
% 3.30/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.30/1.00      | ~ m1_connsp_2(X2,sK3,X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.30/1.00      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X0)
% 3.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_953]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_38,negated_conjecture,
% 3.30/1.00      ( v2_pre_topc(sK2) ),
% 3.30/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1652,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,X0,sK4,X1)
% 3.30/1.00      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.30/1.00      | ~ m1_connsp_2(X2,sK3,X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.30/1.00      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.30/1.00      | sK2 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_954,c_38]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1653,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 3.30/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.30/1.00      | ~ m1_connsp_2(X1,sK3,X0)
% 3.30/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.30/1.00      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 3.30/1.00      | v2_struct_0(sK2)
% 3.30/1.00      | ~ l1_pre_topc(sK2)
% 3.30/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_1652]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_39,negated_conjecture,
% 3.30/1.00      ( ~ v2_struct_0(sK2) ),
% 3.30/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_37,negated_conjecture,
% 3.30/1.00      ( l1_pre_topc(sK2) ),
% 3.30/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_31,negated_conjecture,
% 3.30/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 3.30/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1657,plain,
% 3.30/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_connsp_2(X1,sK3,X0)
% 3.30/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.30/1.00      | r1_tmap_1(sK3,sK2,sK4,X0)
% 3.30/1.00      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 3.30/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_1653,c_39,c_37,c_31]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1658,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 3.30/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.30/1.00      | ~ m1_connsp_2(X1,sK3,X0)
% 3.30/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 3.30/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_1657]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8138,plain,
% 3.30/1.00      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.30/1.00      | r1_tmap_1(sK3,sK2,sK4,X0) = iProver_top
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0) != iProver_top
% 3.30/1.00      | m1_connsp_2(X1,sK3,X0) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/1.00      | r1_tarski(X1,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1658]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8437,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,X0) = iProver_top
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0) != iProver_top
% 3.30/1.00      | m1_connsp_2(X1,sK3,X0) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/1.00      | r1_tarski(X1,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(equality_resolution_simp,[status(thm)],[c_8138]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_12068,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 3.30/1.00      | m1_connsp_2(X0,sK3,sK7) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/1.00      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8202,c_8437]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_27,negated_conjecture,
% 3.30/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8149,plain,
% 3.30/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8163,plain,
% 3.30/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 3.30/1.00      inference(light_normalisation,[status(thm)],[c_8149,c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1922,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.30/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | sK3 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_35]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1923,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK3,X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | v2_struct_0(sK3)
% 3.30/1.00      | ~ l1_pre_topc(sK3) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_1922]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1927,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK3,X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_1923,c_36,c_34]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8720,plain,
% 3.30/1.00      ( ~ m1_connsp_2(X0,sK3,sK7)
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1927]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8721,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK3,sK7) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.30/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_8720]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_22,plain,
% 3.30/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.30/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.30/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.30/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 3.30/1.00      | ~ m1_pre_topc(X4,X0)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.30/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.30/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.30/1.00      | ~ v1_funct_1(X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X4)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_20,plain,
% 3.30/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.30/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.30/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.30/1.00      | ~ m1_pre_topc(X4,X0)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.30/1.00      | ~ v1_funct_1(X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X4)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_210,plain,
% 3.30/1.00      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.30/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.30/1.00      | ~ r1_tmap_1(X0,X1,X2,X3)
% 3.30/1.00      | ~ m1_pre_topc(X4,X0)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.30/1.00      | ~ v1_funct_1(X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X4)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X0) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_22,c_20]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_211,plain,
% 3.30/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.30/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.30/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.30/1.00      | ~ m1_pre_topc(X4,X0)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.30/1.00      | ~ v1_funct_1(X2)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X4)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_210]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_723,plain,
% 3.30/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.30/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.30/1.00      | ~ m1_pre_topc(X4,X0)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.30/1.00      | ~ v1_funct_1(X2)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X4)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.30/1.00      | sK4 != X2 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_211,c_32]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_724,plain,
% 3.30/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.30/1.00      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 3.30/1.00      | ~ m1_pre_topc(X0,X2)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.30/1.00      | ~ v1_funct_1(sK4)
% 3.30/1.00      | v2_struct_0(X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X2)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X2)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_723]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_728,plain,
% 3.30/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_pre_topc(X0,X2)
% 3.30/1.00      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 3.30/1.00      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.30/1.00      | v2_struct_0(X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X2)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X2)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_724,c_33]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_729,plain,
% 3.30/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.30/1.00      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 3.30/1.00      | ~ m1_pre_topc(X0,X2)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X2)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ l1_pre_topc(X2)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X2)
% 3.30/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_728]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_764,plain,
% 3.30/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.30/1.00      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 3.30/1.00      | ~ m1_pre_topc(X0,X2)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | v2_struct_0(X2)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ l1_pre_topc(X2)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X2)
% 3.30/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_729,c_7]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_996,plain,
% 3.30/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.30/1.00      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 3.30/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(X2)
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X2)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X2)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.30/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.30/1.00      | sK3 != X2
% 3.30/1.00      | sK5 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_764]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_997,plain,
% 3.30/1.00      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 3.30/1.00      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | v2_struct_0(sK3)
% 3.30/1.00      | v2_struct_0(sK5)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ l1_pre_topc(sK3)
% 3.30/1.00      | ~ v2_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(sK3)
% 3.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_996]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1001,plain,
% 3.30/1.00      ( ~ v2_pre_topc(X0)
% 3.30/1.00      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 3.30/1.00      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_997,c_36,c_35,c_34,c_30]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1002,plain,
% 3.30/1.00      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 3.30/1.00      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | ~ v2_pre_topc(X0)
% 3.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_1001]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1628,plain,
% 3.30/1.00      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 3.30/1.00      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.30/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.30/1.00      | v2_struct_0(X0)
% 3.30/1.00      | ~ l1_pre_topc(X0)
% 3.30/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.30/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.30/1.00      | sK2 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_1002,c_38]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1629,plain,
% 3.30/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.30/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.30/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.30/1.00      | v2_struct_0(sK2)
% 3.30/1.00      | ~ l1_pre_topc(sK2)
% 3.30/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_1628]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1633,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.30/1.00      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 3.30/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_1629,c_39,c_37,c_31]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1634,plain,
% 3.30/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.30/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.30/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_1633]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8139,plain,
% 3.30/1.00      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.30/1.00      | r1_tmap_1(sK3,sK2,sK4,X0) != iProver_top
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0) = iProver_top
% 3.30/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1634]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8360,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,X0) != iProver_top
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0) = iProver_top
% 3.30/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(equality_resolution_simp,[status(thm)],[c_8139]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_23,negated_conjecture,
% 3.30/1.00      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 3.30/1.00      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 3.30/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8152,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8225,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 3.30/1.00      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 3.30/1.00      inference(light_normalisation,[status(thm)],[c_8152,c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_11383,plain,
% 3.30/1.00      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 3.30/1.00      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8360,c_8225]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_12084,plain,
% 3.30/1.00      ( m1_connsp_2(X0,sK3,sK7) != iProver_top
% 3.30/1.00      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_12068,c_53,c_8163,c_8721,c_11383]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_12093,plain,
% 3.30/1.00      ( r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top
% 3.30/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 3.30/1.00      | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_11503,c_12084]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(contradiction,plain,
% 3.30/1.00      ( $false ),
% 3.30/1.00      inference(minisat,[status(thm)],[c_20458,c_12093,c_11129,c_8163]) ).
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  ------                               Statistics
% 3.30/1.00  
% 3.30/1.00  ------ General
% 3.30/1.00  
% 3.30/1.00  abstr_ref_over_cycles:                  0
% 3.30/1.00  abstr_ref_under_cycles:                 0
% 3.30/1.00  gc_basic_clause_elim:                   0
% 3.30/1.00  forced_gc_time:                         0
% 3.30/1.00  parsing_time:                           0.009
% 3.30/1.00  unif_index_cands_time:                  0.
% 3.30/1.00  unif_index_add_time:                    0.
% 3.30/1.00  orderings_time:                         0.
% 3.30/1.00  out_proof_time:                         0.019
% 3.30/1.00  total_time:                             0.46
% 3.30/1.00  num_of_symbols:                         60
% 3.30/1.00  num_of_terms:                           10020
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing
% 3.30/1.00  
% 3.30/1.00  num_of_splits:                          4
% 3.30/1.00  num_of_split_atoms:                     4
% 3.30/1.00  num_of_reused_defs:                     0
% 3.30/1.00  num_eq_ax_congr_red:                    14
% 3.30/1.00  num_of_sem_filtered_clauses:            1
% 3.30/1.00  num_of_subtypes:                        0
% 3.30/1.00  monotx_restored_types:                  0
% 3.30/1.00  sat_num_of_epr_types:                   0
% 3.30/1.00  sat_num_of_non_cyclic_types:            0
% 3.30/1.00  sat_guarded_non_collapsed_types:        0
% 3.30/1.00  num_pure_diseq_elim:                    0
% 3.30/1.00  simp_replaced_by:                       0
% 3.30/1.00  res_preprocessed:                       161
% 3.30/1.00  prep_upred:                             0
% 3.30/1.00  prep_unflattend:                        343
% 3.30/1.00  smt_new_axioms:                         0
% 3.30/1.00  pred_elim_cands:                        13
% 3.30/1.00  pred_elim:                              7
% 3.30/1.00  pred_elim_cl:                           -5
% 3.30/1.00  pred_elim_cycles:                       13
% 3.30/1.00  merged_defs:                            12
% 3.30/1.00  merged_defs_ncl:                        0
% 3.30/1.00  bin_hyper_res:                          12
% 3.30/1.00  prep_cycles:                            3
% 3.30/1.00  pred_elim_time:                         0.103
% 3.30/1.00  splitting_time:                         0.
% 3.30/1.00  sem_filter_time:                        0.
% 3.30/1.00  monotx_time:                            0.
% 3.30/1.00  subtype_inf_time:                       0.
% 3.30/1.00  
% 3.30/1.00  ------ Problem properties
% 3.30/1.00  
% 3.30/1.00  clauses:                                47
% 3.30/1.00  conjectures:                            6
% 3.30/1.00  epr:                                    3
% 3.30/1.00  horn:                                   46
% 3.30/1.00  ground:                                 12
% 3.30/1.00  unary:                                  7
% 3.30/1.00  binary:                                 8
% 3.30/1.00  lits:                                   146
% 3.30/1.00  lits_eq:                                8
% 3.30/1.00  fd_pure:                                0
% 3.30/1.00  fd_pseudo:                              0
% 3.30/1.00  fd_cond:                                0
% 3.30/1.00  fd_pseudo_cond:                         1
% 3.30/1.00  ac_symbols:                             0
% 3.30/1.00  
% 3.30/1.00  ------ Propositional Solver
% 3.30/1.00  
% 3.30/1.00  prop_solver_calls:                      26
% 3.30/1.00  prop_fast_solver_calls:                 4260
% 3.30/1.00  smt_solver_calls:                       0
% 3.30/1.00  smt_fast_solver_calls:                  0
% 3.30/1.00  prop_num_of_clauses:                    5359
% 3.30/1.00  prop_preprocess_simplified:             13093
% 3.30/1.00  prop_fo_subsumed:                       218
% 3.30/1.00  prop_solver_time:                       0.
% 3.30/1.00  smt_solver_time:                        0.
% 3.30/1.00  smt_fast_solver_time:                   0.
% 3.30/1.00  prop_fast_solver_time:                  0.
% 3.30/1.00  prop_unsat_core_time:                   0.
% 3.30/1.00  
% 3.30/1.00  ------ QBF
% 3.30/1.00  
% 3.30/1.00  qbf_q_res:                              0
% 3.30/1.00  qbf_num_tautologies:                    0
% 3.30/1.00  qbf_prep_cycles:                        0
% 3.30/1.00  
% 3.30/1.00  ------ BMC1
% 3.30/1.00  
% 3.30/1.00  bmc1_current_bound:                     -1
% 3.30/1.00  bmc1_last_solved_bound:                 -1
% 3.30/1.00  bmc1_unsat_core_size:                   -1
% 3.30/1.00  bmc1_unsat_core_parents_size:           -1
% 3.30/1.00  bmc1_merge_next_fun:                    0
% 3.30/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.30/1.00  
% 3.30/1.00  ------ Instantiation
% 3.30/1.00  
% 3.30/1.00  inst_num_of_clauses:                    1411
% 3.30/1.00  inst_num_in_passive:                    120
% 3.30/1.00  inst_num_in_active:                     909
% 3.30/1.00  inst_num_in_unprocessed:                383
% 3.30/1.00  inst_num_of_loops:                      950
% 3.30/1.00  inst_num_of_learning_restarts:          0
% 3.30/1.00  inst_num_moves_active_passive:          36
% 3.30/1.00  inst_lit_activity:                      0
% 3.30/1.00  inst_lit_activity_moves:                0
% 3.30/1.00  inst_num_tautologies:                   0
% 3.30/1.00  inst_num_prop_implied:                  0
% 3.30/1.00  inst_num_existing_simplified:           0
% 3.30/1.00  inst_num_eq_res_simplified:             0
% 3.30/1.00  inst_num_child_elim:                    0
% 3.30/1.00  inst_num_of_dismatching_blockings:      489
% 3.30/1.00  inst_num_of_non_proper_insts:           2179
% 3.30/1.00  inst_num_of_duplicates:                 0
% 3.30/1.00  inst_inst_num_from_inst_to_res:         0
% 3.30/1.00  inst_dismatching_checking_time:         0.
% 3.30/1.00  
% 3.30/1.00  ------ Resolution
% 3.30/1.00  
% 3.30/1.00  res_num_of_clauses:                     0
% 3.30/1.00  res_num_in_passive:                     0
% 3.30/1.00  res_num_in_active:                      0
% 3.30/1.00  res_num_of_loops:                       164
% 3.30/1.00  res_forward_subset_subsumed:            258
% 3.30/1.00  res_backward_subset_subsumed:           11
% 3.30/1.00  res_forward_subsumed:                   6
% 3.30/1.00  res_backward_subsumed:                  2
% 3.30/1.00  res_forward_subsumption_resolution:     24
% 3.30/1.00  res_backward_subsumption_resolution:    0
% 3.30/1.00  res_clause_to_clause_subsumption:       2978
% 3.30/1.00  res_orphan_elimination:                 0
% 3.30/1.00  res_tautology_del:                      282
% 3.30/1.00  res_num_eq_res_simplified:              2
% 3.30/1.00  res_num_sel_changes:                    0
% 3.30/1.00  res_moves_from_active_to_pass:          0
% 3.30/1.00  
% 3.30/1.00  ------ Superposition
% 3.30/1.00  
% 3.30/1.00  sup_time_total:                         0.
% 3.30/1.00  sup_time_generating:                    0.
% 3.30/1.00  sup_time_sim_full:                      0.
% 3.30/1.00  sup_time_sim_immed:                     0.
% 3.30/1.00  
% 3.30/1.00  sup_num_of_clauses:                     227
% 3.30/1.00  sup_num_in_active:                      187
% 3.30/1.00  sup_num_in_passive:                     40
% 3.30/1.00  sup_num_of_loops:                       189
% 3.30/1.00  sup_fw_superposition:                   172
% 3.30/1.00  sup_bw_superposition:                   95
% 3.30/1.00  sup_immediate_simplified:               44
% 3.30/1.00  sup_given_eliminated:                   2
% 3.30/1.00  comparisons_done:                       0
% 3.30/1.00  comparisons_avoided:                    0
% 3.30/1.00  
% 3.30/1.00  ------ Simplifications
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  sim_fw_subset_subsumed:                 25
% 3.30/1.00  sim_bw_subset_subsumed:                 3
% 3.30/1.00  sim_fw_subsumed:                        26
% 3.30/1.00  sim_bw_subsumed:                        4
% 3.30/1.00  sim_fw_subsumption_res:                 22
% 3.30/1.00  sim_bw_subsumption_res:                 0
% 3.30/1.00  sim_tautology_del:                      31
% 3.30/1.00  sim_eq_tautology_del:                   1
% 3.30/1.00  sim_eq_res_simp:                        2
% 3.30/1.00  sim_fw_demodulated:                     0
% 3.30/1.00  sim_bw_demodulated:                     0
% 3.30/1.00  sim_light_normalised:                   3
% 3.30/1.00  sim_joinable_taut:                      0
% 3.30/1.00  sim_joinable_simp:                      0
% 3.30/1.00  sim_ac_normalised:                      0
% 3.30/1.00  sim_smt_subsumption:                    0
% 3.30/1.00  
%------------------------------------------------------------------------------
