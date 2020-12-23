%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:51 EST 2020

% Result     : Theorem 31.17s
% Output     : CNFRefutation 31.17s
% Verified   : 
% Statistics : Number of formulae       :  346 (6830 expanded)
%              Number of clauses        :  221 (1921 expanded)
%              Number of leaves         :   41 (1933 expanded)
%              Depth                    :   25
%              Number of atoms          : 1259 (42925 expanded)
%              Number of equality atoms :  521 (3684 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v5_pre_topc(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v5_pre_topc(sK8,X0,X1)
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ~ v5_pre_topc(X2,X0,sK7)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK7)
        & v2_pre_topc(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK6,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK6)
      & v1_tdlat_3(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    & v1_funct_1(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & l1_pre_topc(sK6)
    & v1_tdlat_3(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f52,f85,f84,f83])).

fof(f139,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f86])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f116,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f115,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f141,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f86])).

fof(f144,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f86])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f71])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2))))
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2))))
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f72,f73])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f140,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f86])).

fof(f137,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f86])).

fof(f142,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f86])).

fof(f145,plain,(
    ~ v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f86])).

fof(f143,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f86])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f67])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
        & v3_pre_topc(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
                    & v3_pre_topc(sK2(X0,X1,X2),X1)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f68,f69])).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f138,plain,(
    v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f86])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f75,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f76,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f75])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f76,f77])).

fof(f131,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f95,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f63])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f148,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f99])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(sK2(X0,X1,X2),X1)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f80,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f79])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f80,f81])).

fof(f134,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f130,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f114,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f149,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f113,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_56,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_2155,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_29,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2182,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3528,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_2182])).

cnf(c_28,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2183,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3835,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_3528,c_2183])).

cnf(c_54,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_2157,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_3527,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2157,c_2182])).

cnf(c_3672,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_3527,c_2183])).

cnf(c_51,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_2160,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_3837,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_struct_0(sK7)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3672,c_2160])).

cnf(c_4161,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3835,c_3837])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_2170,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_8999,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK3(X1,sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3672,c_2170])).

cnf(c_9009,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK3(X1,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8999,c_3672])).

cnf(c_55,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_62,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_63,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_9586,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK3(X1,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9009,c_62,c_63])).

cnf(c_9587,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK3(X1,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9586])).

cnf(c_9601,plain,
    ( v1_funct_2(X0,u1_struct_0(sK6),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,sK6,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK3(sK6,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3835,c_9587])).

cnf(c_9625,plain,
    ( v1_funct_2(X0,k2_struct_0(sK6),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,sK6,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK3(sK6,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9601,c_3835])).

cnf(c_58,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_59,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_61,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_10049,plain,
    ( v1_funct_2(X0,k2_struct_0(sK6),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,sK6,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK3(sK6,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9625,c_59,c_61])).

cnf(c_10062,plain,
    ( v1_funct_2(sK8,k2_struct_0(sK6),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4161,c_10049])).

cnf(c_53,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_64,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_50,negated_conjecture,
    ( ~ v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_67,plain,
    ( v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_52,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_2159,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_3838,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),k2_struct_0(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3672,c_2159])).

cnf(c_4162,plain,
    ( v1_funct_2(sK8,k2_struct_0(sK6),k2_struct_0(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3835,c_3838])).

cnf(c_10309,plain,
    ( m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10062,c_64,c_67,c_4162])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2195,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10314,plain,
    ( r1_tarski(sK3(sK6,sK7,sK8),k2_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10309,c_2195])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2172,plain,
    ( k2_struct_0(X0) = k1_xboole_0
    | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(X1,X2,X0) != iProver_top
    | v3_pre_topc(X3,X0) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X0),X1,X3),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_12670,plain,
    ( k2_struct_0(sK7) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) != iProver_top
    | v3_pre_topc(X2,sK7) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3672,c_2172])).

cnf(c_12681,plain,
    ( k2_struct_0(sK7) = k1_xboole_0
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) != iProver_top
    | v3_pre_topc(X2,sK7) != iProver_top
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,X2),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK7))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12670,c_3672])).

cnf(c_57,negated_conjecture,
    ( v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_46,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_2878,plain,
    ( v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_3221,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),sK6)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_2878])).

cnf(c_3783,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_tdlat_3(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_3221])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_3784,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | v5_pre_topc(sK8,sK6,sK7)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_1(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | k2_struct_0(sK7) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2896,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_5017,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_2896])).

cnf(c_13768,plain,
    ( k2_struct_0(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12681,c_58,c_57,c_56,c_54,c_53,c_52,c_51,c_50,c_3783,c_3784,c_5017])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2203,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2205,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4981,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_2205])).

cnf(c_4596,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4161,c_2195])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2200,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6071,plain,
    ( k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)) = sK8
    | r1_tarski(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4596,c_2200])).

cnf(c_6322,plain,
    ( k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)) = sK8
    | v1_xboole_0(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4981,c_6071])).

cnf(c_13793,plain,
    ( k2_zfmisc_1(k2_struct_0(sK6),k1_xboole_0) = sK8
    | v1_xboole_0(k2_zfmisc_1(k2_struct_0(sK6),k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13768,c_6322])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f148])).

cnf(c_13839,plain,
    ( sK8 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13793,c_10])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_185,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3903,plain,
    ( r1_tarski(sK8,X0)
    | r2_hidden(sK1(sK8,X0),sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3909,plain,
    ( r1_tarski(sK8,X0) = iProver_top
    | r2_hidden(sK1(sK8,X0),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3903])).

cnf(c_3911,plain,
    ( r1_tarski(sK8,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK8,k1_xboole_0),sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3909])).

cnf(c_3934,plain,
    ( ~ r1_tarski(X0,sK8)
    | ~ r1_tarski(sK8,X0)
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3935,plain,
    ( sK8 = X0
    | r1_tarski(X0,sK8) != iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3934])).

cnf(c_3937,plain,
    ( sK8 = k1_xboole_0
    | r1_tarski(sK8,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3935])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_5332,plain,
    ( r1_tarski(k1_xboole_0,sK8) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5335,plain,
    ( r1_tarski(k1_xboole_0,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5332])).

cnf(c_9848,plain,
    ( ~ r2_hidden(sK1(sK8,X0),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9849,plain,
    ( r2_hidden(sK1(sK8,X0),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9848])).

cnf(c_9851,plain,
    ( r2_hidden(sK1(sK8,k1_xboole_0),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9849])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11310,plain,
    ( v1_xboole_0(k2_struct_0(sK7)) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_4161,c_2192])).

cnf(c_13777,plain,
    ( v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13768,c_11310])).

cnf(c_15422,plain,
    ( sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13839,c_185,c_3911,c_3937,c_5335,c_9851,c_13777])).

cnf(c_16507,plain,
    ( r1_tarski(sK3(sK6,sK7,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10314,c_13768,c_15422])).

cnf(c_16511,plain,
    ( sK3(sK6,sK7,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3(sK6,sK7,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16507,c_2200])).

cnf(c_2198,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_106220,plain,
    ( sK3(sK6,sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16511,c_2198])).

cnf(c_13803,plain,
    ( u1_struct_0(sK7) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13768,c_3672])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2171,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_14508,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_13803,c_2171])).

cnf(c_14564,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14508,c_13803])).

cnf(c_14565,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14564,c_10])).

cnf(c_177,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_943,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4147,plain,
    ( X0 != X1
    | k2_struct_0(X2) != X1
    | k2_struct_0(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_6675,plain,
    ( X0 != k1_xboole_0
    | k2_struct_0(sK7) = X0
    | k2_struct_0(sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4147])).

cnf(c_7540,plain,
    ( k2_struct_0(sK7) = sK8
    | k2_struct_0(sK7) != k1_xboole_0
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6675])).

cnf(c_962,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2804,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK8)
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_7542,plain,
    ( v1_funct_1(k2_struct_0(sK7))
    | ~ v1_funct_1(sK8)
    | k2_struct_0(sK7) != sK8 ),
    inference(instantiation,[status(thm)],[c_2804])).

cnf(c_7543,plain,
    ( k2_struct_0(sK7) != sK8
    | v1_funct_1(k2_struct_0(sK7)) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7542])).

cnf(c_10788,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3672,c_2171])).

cnf(c_10798,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10788,c_3672])).

cnf(c_11691,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10798,c_62,c_63])).

cnf(c_11692,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11691])).

cnf(c_13776,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13768,c_11692])).

cnf(c_14002,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13776,c_10])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v3_pre_topc(sK2(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_14167,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | v5_pre_topc(sK8,sK6,sK7)
    | v3_pre_topc(sK2(sK6,sK7,sK8),sK7)
    | ~ v1_funct_1(sK8)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | k2_struct_0(sK7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_51])).

cnf(c_14178,plain,
    ( k2_struct_0(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14167,c_58,c_57,c_56,c_54,c_53,c_52,c_51,c_50,c_3783,c_3784,c_5017])).

cnf(c_946,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_14209,plain,
    ( r1_tarski(X0,k2_struct_0(sK7))
    | ~ r1_tarski(X1,k1_xboole_0)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_14178,c_946])).

cnf(c_942,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_16946,plain,
    ( r1_tarski(X0,k2_struct_0(sK7))
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14209,c_942])).

cnf(c_5251,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(X1) ),
    inference(resolution,[status(thm)],[c_6,c_962])).

cnf(c_18147,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k2_struct_0(sK7),X0)
    | v1_funct_1(X0)
    | ~ v1_funct_1(k2_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_16946,c_5251])).

cnf(c_18152,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_struct_0(sK7),X0) != iProver_top
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(k2_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18147])).

cnf(c_949,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9803,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_949,c_942])).

cnf(c_14202,plain,
    ( m1_subset_1(k2_struct_0(sK7),X0)
    | ~ m1_subset_1(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_14178,c_9803])).

cnf(c_15461,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | r1_tarski(k2_struct_0(sK7),X0) ),
    inference(resolution,[status(thm)],[c_14202,c_16])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_18319,plain,
    ( r1_tarski(k2_struct_0(sK7),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_15461,c_15])).

cnf(c_18320,plain,
    ( r1_tarski(k2_struct_0(sK7),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18319])).

cnf(c_8095,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_943,c_942])).

cnf(c_21012,plain,
    ( k1_xboole_0 = k2_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_8095,c_14178])).

cnf(c_21047,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK7))
    | r1_tarski(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_21012,c_946])).

cnf(c_24041,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK7))
    | r1_tarski(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_21047,c_942])).

cnf(c_24042,plain,
    ( r1_tarski(X0,k2_struct_0(sK7)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24041])).

cnf(c_948,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_9805,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_949,c_948])).

cnf(c_48932,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK7)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_9805,c_14178])).

cnf(c_49782,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK7)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_48932,c_942])).

cnf(c_50359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(X0,k2_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_49782,c_16])).

cnf(c_50360,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50359])).

cnf(c_52030,plain,
    ( l1_pre_topc(X1) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14565,c_58,c_57,c_56,c_54,c_53,c_64,c_52,c_51,c_50,c_177,c_185,c_3783,c_3784,c_3911,c_3937,c_5017,c_5335,c_7540,c_7543,c_9851,c_13777,c_14002,c_18152,c_18320,c_24042,c_50360])).

cnf(c_52031,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,X1,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_52030])).

cnf(c_52046,plain,
    ( v1_funct_2(X0,u1_struct_0(sK6),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK6,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_pre_topc(sK6,k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,sK3(sK6,sK7,X0))),k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(sK6,sK7,X0)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3835,c_52031])).

cnf(c_52067,plain,
    ( v1_funct_2(X0,k2_struct_0(sK6),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK6,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_pre_topc(sK6,k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,sK3(sK6,sK7,X0))),k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(sK6,sK7,X0)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_52046,c_3835])).

cnf(c_52659,plain,
    ( v1_funct_2(X0,k2_struct_0(sK6),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK6,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_pre_topc(sK6,k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,sK3(sK6,sK7,X0))),k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(sK6,sK7,X0)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52067,c_59,c_61])).

cnf(c_52669,plain,
    ( v1_funct_2(X0,k2_struct_0(sK6),k1_xboole_0) != iProver_top
    | v5_pre_topc(X0,sK6,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_pre_topc(sK6,k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,sK3(sK6,sK7,X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4981,c_52659])).

cnf(c_106243,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK6),k1_xboole_0) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_pre_topc(sK6,k8_relset_1(k2_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_106220,c_52669])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2189,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9267,plain,
    ( k8_relset_1(k2_struct_0(sK6),k2_struct_0(sK7),sK8,k2_struct_0(sK7)) = k1_relset_1(k2_struct_0(sK6),k2_struct_0(sK7),sK8) ),
    inference(superposition,[status(thm)],[c_4161,c_2189])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2190,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5816,plain,
    ( k1_relset_1(k2_struct_0(sK6),k2_struct_0(sK7),sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_4161,c_2190])).

cnf(c_9279,plain,
    ( k8_relset_1(k2_struct_0(sK6),k2_struct_0(sK7),sK8,k2_struct_0(sK7)) = k1_relat_1(sK8) ),
    inference(light_normalisation,[status(thm)],[c_9267,c_5816])).

cnf(c_17742,plain,
    ( k8_relset_1(k2_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_9279,c_13768,c_15422])).

cnf(c_2191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17744,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_17742,c_2191])).

cnf(c_17745,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17744,c_10])).

cnf(c_168,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_170,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_179,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_17921,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17745,c_170,c_179])).

cnf(c_49,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_2162,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_43,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2168,plain,
    ( v1_tdlat_3(X0) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2387,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2162,c_2168])).

cnf(c_27482,plain,
    ( v4_pre_topc(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
    | v1_tdlat_3(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3835,c_2387])).

cnf(c_60,plain,
    ( v1_tdlat_3(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_28056,plain,
    ( v4_pre_topc(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27482,c_60,c_61])).

cnf(c_28069,plain,
    ( v4_pre_topc(k1_relat_1(k1_xboole_0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_17921,c_28056])).

cnf(c_31,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2180,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18035,plain,
    ( k2_pre_topc(sK6,X0) = X0
    | v4_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3835,c_2180])).

cnf(c_18266,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
    | v4_pre_topc(X0,sK6) != iProver_top
    | k2_pre_topc(sK6,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18035,c_61])).

cnf(c_18267,plain,
    ( k2_pre_topc(sK6,X0) = X0
    | v4_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_18266])).

cnf(c_18278,plain,
    ( k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0)
    | v4_pre_topc(k1_relat_1(k1_xboole_0),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_17921,c_18267])).

cnf(c_28341,plain,
    ( k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_28069,c_18278])).

cnf(c_106284,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK6),k1_xboole_0) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_106243,c_17742,c_28341])).

cnf(c_2161,plain,
    ( v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_15429,plain,
    ( v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15422,c_2161])).

cnf(c_13802,plain,
    ( v1_funct_2(sK8,k2_struct_0(sK6),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13768,c_4162])).

cnf(c_15427,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK6),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15422,c_13802])).

cnf(c_25,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_944,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_9685,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(resolution,[status(thm)],[c_25,c_944])).

cnf(c_9690,plain,
    ( v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9685])).

cnf(c_9692,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) != iProver_top
    | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9690])).

cnf(c_6745,plain,
    ( r1_tarski(k1_xboole_0,k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6749,plain,
    ( r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6745])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2185,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3422,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_2185])).

cnf(c_4595,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3422,c_2195])).

cnf(c_4615,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4595])).

cnf(c_4226,plain,
    ( ~ r1_tarski(X0,k6_partfun1(X1))
    | ~ r1_tarski(k6_partfun1(X1),X0)
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4228,plain,
    ( ~ r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4226])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3127,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_18,c_15])).

cnf(c_3274,plain,
    ( v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_3127,c_9])).

cnf(c_3275,plain,
    ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3274])).

cnf(c_3277,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3275])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2194,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3108,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_2194])).

cnf(c_953,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3057,plain,
    ( v1_partfun1(X0,X1)
    | ~ v1_partfun1(k6_partfun1(X2),X2)
    | X1 != X2
    | X0 != k6_partfun1(X2) ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_3058,plain,
    ( X0 != X1
    | X2 != k6_partfun1(X1)
    | v1_partfun1(X2,X0) = iProver_top
    | v1_partfun1(k6_partfun1(X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3057])).

cnf(c_3060,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3058])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f149])).

cnf(c_176,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_175,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_27,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_134,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_136,plain,
    ( v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_106284,c_15429,c_15427,c_9692,c_6749,c_4615,c_4228,c_3277,c_3108,c_3060,c_185,c_179,c_176,c_175,c_170,c_136])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.17/4.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.17/4.51  
% 31.17/4.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.17/4.51  
% 31.17/4.51  ------  iProver source info
% 31.17/4.51  
% 31.17/4.51  git: date: 2020-06-30 10:37:57 +0100
% 31.17/4.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.17/4.51  git: non_committed_changes: false
% 31.17/4.51  git: last_make_outside_of_git: false
% 31.17/4.51  
% 31.17/4.51  ------ 
% 31.17/4.51  ------ Parsing...
% 31.17/4.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.17/4.51  
% 31.17/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 31.17/4.51  
% 31.17/4.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.17/4.51  
% 31.17/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.17/4.51  ------ Proving...
% 31.17/4.51  ------ Problem Properties 
% 31.17/4.51  
% 31.17/4.51  
% 31.17/4.51  clauses                                 58
% 31.17/4.51  conjectures                             9
% 31.17/4.51  EPR                                     15
% 31.17/4.51  Horn                                    46
% 31.17/4.51  unary                                   19
% 31.17/4.51  binary                                  13
% 31.17/4.51  lits                                    198
% 31.17/4.51  lits eq                                 22
% 31.17/4.51  fd_pure                                 0
% 31.17/4.51  fd_pseudo                               0
% 31.17/4.51  fd_cond                                 1
% 31.17/4.51  fd_pseudo_cond                          2
% 31.17/4.51  AC symbols                              0
% 31.17/4.51  
% 31.17/4.51  ------ Input Options Time Limit: Unbounded
% 31.17/4.51  
% 31.17/4.51  
% 31.17/4.51  ------ 
% 31.17/4.51  Current options:
% 31.17/4.51  ------ 
% 31.17/4.51  
% 31.17/4.51  
% 31.17/4.51  
% 31.17/4.51  
% 31.17/4.51  ------ Proving...
% 31.17/4.51  
% 31.17/4.51  
% 31.17/4.51  % SZS status Theorem for theBenchmark.p
% 31.17/4.51  
% 31.17/4.51  % SZS output start CNFRefutation for theBenchmark.p
% 31.17/4.51  
% 31.17/4.51  fof(f26,conjecture,(
% 31.17/4.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f27,negated_conjecture,(
% 31.17/4.51    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 31.17/4.51    inference(negated_conjecture,[],[f26])).
% 31.17/4.51  
% 31.17/4.51  fof(f51,plain,(
% 31.17/4.51    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 31.17/4.51    inference(ennf_transformation,[],[f27])).
% 31.17/4.51  
% 31.17/4.51  fof(f52,plain,(
% 31.17/4.51    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 31.17/4.51    inference(flattening,[],[f51])).
% 31.17/4.51  
% 31.17/4.51  fof(f85,plain,(
% 31.17/4.51    ( ! [X0,X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~v5_pre_topc(sK8,X0,X1) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 31.17/4.51    introduced(choice_axiom,[])).
% 31.17/4.51  
% 31.17/4.51  fof(f84,plain,(
% 31.17/4.51    ( ! [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (~v5_pre_topc(X2,X0,sK7) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7)) & v1_funct_1(X2)) & l1_pre_topc(sK7) & v2_pre_topc(sK7))) )),
% 31.17/4.51    introduced(choice_axiom,[])).
% 31.17/4.51  
% 31.17/4.51  fof(f83,plain,(
% 31.17/4.51    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v5_pre_topc(X2,sK6,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK6) & v1_tdlat_3(sK6) & v2_pre_topc(sK6))),
% 31.17/4.51    introduced(choice_axiom,[])).
% 31.17/4.51  
% 31.17/4.51  fof(f86,plain,(
% 31.17/4.51    ((~v5_pre_topc(sK8,sK6,sK7) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK8)) & l1_pre_topc(sK7) & v2_pre_topc(sK7)) & l1_pre_topc(sK6) & v1_tdlat_3(sK6) & v2_pre_topc(sK6)),
% 31.17/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f52,f85,f84,f83])).
% 31.17/4.51  
% 31.17/4.51  fof(f139,plain,(
% 31.17/4.51    l1_pre_topc(sK6)),
% 31.17/4.51    inference(cnf_transformation,[],[f86])).
% 31.17/4.51  
% 31.17/4.51  fof(f19,axiom,(
% 31.17/4.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f38,plain,(
% 31.17/4.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 31.17/4.51    inference(ennf_transformation,[],[f19])).
% 31.17/4.51  
% 31.17/4.51  fof(f116,plain,(
% 31.17/4.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f38])).
% 31.17/4.51  
% 31.17/4.51  fof(f18,axiom,(
% 31.17/4.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f37,plain,(
% 31.17/4.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 31.17/4.51    inference(ennf_transformation,[],[f18])).
% 31.17/4.51  
% 31.17/4.51  fof(f115,plain,(
% 31.17/4.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f37])).
% 31.17/4.51  
% 31.17/4.51  fof(f141,plain,(
% 31.17/4.51    l1_pre_topc(sK7)),
% 31.17/4.51    inference(cnf_transformation,[],[f86])).
% 31.17/4.51  
% 31.17/4.51  fof(f144,plain,(
% 31.17/4.51    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 31.17/4.51    inference(cnf_transformation,[],[f86])).
% 31.17/4.51  
% 31.17/4.51  fof(f22,axiom,(
% 31.17/4.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f43,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 31.17/4.51    inference(ennf_transformation,[],[f22])).
% 31.17/4.51  
% 31.17/4.51  fof(f44,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(flattening,[],[f43])).
% 31.17/4.51  
% 31.17/4.51  fof(f71,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(nnf_transformation,[],[f44])).
% 31.17/4.51  
% 31.17/4.51  fof(f72,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(rectify,[],[f71])).
% 31.17/4.51  
% 31.17/4.51  fof(f73,plain,(
% 31.17/4.51    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2)))) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 31.17/4.51    introduced(choice_axiom,[])).
% 31.17/4.51  
% 31.17/4.51  fof(f74,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2)))) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f72,f73])).
% 31.17/4.51  
% 31.17/4.51  fof(f128,plain,(
% 31.17/4.51    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f74])).
% 31.17/4.51  
% 31.17/4.51  fof(f140,plain,(
% 31.17/4.51    v2_pre_topc(sK7)),
% 31.17/4.51    inference(cnf_transformation,[],[f86])).
% 31.17/4.51  
% 31.17/4.51  fof(f137,plain,(
% 31.17/4.51    v2_pre_topc(sK6)),
% 31.17/4.51    inference(cnf_transformation,[],[f86])).
% 31.17/4.51  
% 31.17/4.51  fof(f142,plain,(
% 31.17/4.51    v1_funct_1(sK8)),
% 31.17/4.51    inference(cnf_transformation,[],[f86])).
% 31.17/4.51  
% 31.17/4.51  fof(f145,plain,(
% 31.17/4.51    ~v5_pre_topc(sK8,sK6,sK7)),
% 31.17/4.51    inference(cnf_transformation,[],[f86])).
% 31.17/4.51  
% 31.17/4.51  fof(f143,plain,(
% 31.17/4.51    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))),
% 31.17/4.51    inference(cnf_transformation,[],[f86])).
% 31.17/4.51  
% 31.17/4.51  fof(f9,axiom,(
% 31.17/4.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f65,plain,(
% 31.17/4.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.17/4.51    inference(nnf_transformation,[],[f9])).
% 31.17/4.51  
% 31.17/4.51  fof(f102,plain,(
% 31.17/4.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.17/4.51    inference(cnf_transformation,[],[f65])).
% 31.17/4.51  
% 31.17/4.51  fof(f21,axiom,(
% 31.17/4.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f41,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 31.17/4.51    inference(ennf_transformation,[],[f21])).
% 31.17/4.51  
% 31.17/4.51  fof(f42,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 31.17/4.51    inference(flattening,[],[f41])).
% 31.17/4.51  
% 31.17/4.51  fof(f67,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 31.17/4.51    inference(nnf_transformation,[],[f42])).
% 31.17/4.51  
% 31.17/4.51  fof(f68,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 31.17/4.51    inference(rectify,[],[f67])).
% 31.17/4.51  
% 31.17/4.51  fof(f69,plain,(
% 31.17/4.51    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v3_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 31.17/4.51    introduced(choice_axiom,[])).
% 31.17/4.51  
% 31.17/4.51  fof(f70,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v3_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 31.17/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f68,f69])).
% 31.17/4.51  
% 31.17/4.51  fof(f119,plain,(
% 31.17/4.51    ( ! [X4,X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f70])).
% 31.17/4.51  
% 31.17/4.51  fof(f138,plain,(
% 31.17/4.51    v1_tdlat_3(sK6)),
% 31.17/4.51    inference(cnf_transformation,[],[f86])).
% 31.17/4.51  
% 31.17/4.51  fof(f24,axiom,(
% 31.17/4.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f47,plain,(
% 31.17/4.51    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 31.17/4.51    inference(ennf_transformation,[],[f24])).
% 31.17/4.51  
% 31.17/4.51  fof(f48,plain,(
% 31.17/4.51    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(flattening,[],[f47])).
% 31.17/4.51  
% 31.17/4.51  fof(f75,plain,(
% 31.17/4.51    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(nnf_transformation,[],[f48])).
% 31.17/4.51  
% 31.17/4.51  fof(f76,plain,(
% 31.17/4.51    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(rectify,[],[f75])).
% 31.17/4.51  
% 31.17/4.51  fof(f77,plain,(
% 31.17/4.51    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 31.17/4.51    introduced(choice_axiom,[])).
% 31.17/4.51  
% 31.17/4.51  fof(f78,plain,(
% 31.17/4.51    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f76,f77])).
% 31.17/4.51  
% 31.17/4.51  fof(f131,plain,(
% 31.17/4.51    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f78])).
% 31.17/4.51  
% 31.17/4.51  fof(f125,plain,(
% 31.17/4.51    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f70])).
% 31.17/4.51  
% 31.17/4.51  fof(f13,axiom,(
% 31.17/4.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f32,plain,(
% 31.17/4.51    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.17/4.51    inference(ennf_transformation,[],[f13])).
% 31.17/4.51  
% 31.17/4.51  fof(f107,plain,(
% 31.17/4.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.17/4.51    inference(cnf_transformation,[],[f32])).
% 31.17/4.51  
% 31.17/4.51  fof(f2,axiom,(
% 31.17/4.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f29,plain,(
% 31.17/4.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 31.17/4.51    inference(ennf_transformation,[],[f2])).
% 31.17/4.51  
% 31.17/4.51  fof(f57,plain,(
% 31.17/4.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 31.17/4.51    inference(nnf_transformation,[],[f29])).
% 31.17/4.51  
% 31.17/4.51  fof(f58,plain,(
% 31.17/4.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.17/4.51    inference(rectify,[],[f57])).
% 31.17/4.51  
% 31.17/4.51  fof(f59,plain,(
% 31.17/4.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 31.17/4.51    introduced(choice_axiom,[])).
% 31.17/4.51  
% 31.17/4.51  fof(f60,plain,(
% 31.17/4.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.17/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).
% 31.17/4.51  
% 31.17/4.51  fof(f90,plain,(
% 31.17/4.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f60])).
% 31.17/4.51  
% 31.17/4.51  fof(f1,axiom,(
% 31.17/4.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f53,plain,(
% 31.17/4.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 31.17/4.51    inference(nnf_transformation,[],[f1])).
% 31.17/4.51  
% 31.17/4.51  fof(f54,plain,(
% 31.17/4.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 31.17/4.51    inference(rectify,[],[f53])).
% 31.17/4.51  
% 31.17/4.51  fof(f55,plain,(
% 31.17/4.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 31.17/4.51    introduced(choice_axiom,[])).
% 31.17/4.51  
% 31.17/4.51  fof(f56,plain,(
% 31.17/4.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 31.17/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).
% 31.17/4.51  
% 31.17/4.51  fof(f87,plain,(
% 31.17/4.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f56])).
% 31.17/4.51  
% 31.17/4.51  fof(f4,axiom,(
% 31.17/4.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f61,plain,(
% 31.17/4.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.17/4.51    inference(nnf_transformation,[],[f4])).
% 31.17/4.51  
% 31.17/4.51  fof(f62,plain,(
% 31.17/4.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.17/4.51    inference(flattening,[],[f61])).
% 31.17/4.51  
% 31.17/4.51  fof(f95,plain,(
% 31.17/4.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f62])).
% 31.17/4.51  
% 31.17/4.51  fof(f6,axiom,(
% 31.17/4.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f63,plain,(
% 31.17/4.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.17/4.51    inference(nnf_transformation,[],[f6])).
% 31.17/4.51  
% 31.17/4.51  fof(f64,plain,(
% 31.17/4.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.17/4.51    inference(flattening,[],[f63])).
% 31.17/4.51  
% 31.17/4.51  fof(f99,plain,(
% 31.17/4.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 31.17/4.51    inference(cnf_transformation,[],[f64])).
% 31.17/4.51  
% 31.17/4.51  fof(f148,plain,(
% 31.17/4.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 31.17/4.51    inference(equality_resolution,[],[f99])).
% 31.17/4.51  
% 31.17/4.51  fof(f3,axiom,(
% 31.17/4.51    v1_xboole_0(k1_xboole_0)),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f92,plain,(
% 31.17/4.51    v1_xboole_0(k1_xboole_0)),
% 31.17/4.51    inference(cnf_transformation,[],[f3])).
% 31.17/4.51  
% 31.17/4.51  fof(f5,axiom,(
% 31.17/4.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f96,plain,(
% 31.17/4.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f5])).
% 31.17/4.51  
% 31.17/4.51  fof(f12,axiom,(
% 31.17/4.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f31,plain,(
% 31.17/4.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 31.17/4.51    inference(ennf_transformation,[],[f12])).
% 31.17/4.51  
% 31.17/4.51  fof(f106,plain,(
% 31.17/4.51    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f31])).
% 31.17/4.51  
% 31.17/4.51  fof(f129,plain,(
% 31.17/4.51    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f74])).
% 31.17/4.51  
% 31.17/4.51  fof(f123,plain,(
% 31.17/4.51    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v3_pre_topc(sK2(X0,X1,X2),X1) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f70])).
% 31.17/4.51  
% 31.17/4.51  fof(f103,plain,(
% 31.17/4.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f65])).
% 31.17/4.51  
% 31.17/4.51  fof(f15,axiom,(
% 31.17/4.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f34,plain,(
% 31.17/4.51    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.17/4.51    inference(ennf_transformation,[],[f15])).
% 31.17/4.51  
% 31.17/4.51  fof(f110,plain,(
% 31.17/4.51    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.17/4.51    inference(cnf_transformation,[],[f34])).
% 31.17/4.51  
% 31.17/4.51  fof(f14,axiom,(
% 31.17/4.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f33,plain,(
% 31.17/4.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.17/4.51    inference(ennf_transformation,[],[f14])).
% 31.17/4.51  
% 31.17/4.51  fof(f108,plain,(
% 31.17/4.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.17/4.51    inference(cnf_transformation,[],[f33])).
% 31.17/4.51  
% 31.17/4.51  fof(f25,axiom,(
% 31.17/4.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f49,plain,(
% 31.17/4.51    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 31.17/4.51    inference(ennf_transformation,[],[f25])).
% 31.17/4.51  
% 31.17/4.51  fof(f50,plain,(
% 31.17/4.51    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(flattening,[],[f49])).
% 31.17/4.51  
% 31.17/4.51  fof(f79,plain,(
% 31.17/4.51    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(nnf_transformation,[],[f50])).
% 31.17/4.51  
% 31.17/4.51  fof(f80,plain,(
% 31.17/4.51    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(rectify,[],[f79])).
% 31.17/4.51  
% 31.17/4.51  fof(f81,plain,(
% 31.17/4.51    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 31.17/4.51    introduced(choice_axiom,[])).
% 31.17/4.51  
% 31.17/4.51  fof(f82,plain,(
% 31.17/4.51    ! [X0] : (((v1_tdlat_3(X0) | (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 31.17/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f80,f81])).
% 31.17/4.51  
% 31.17/4.51  fof(f134,plain,(
% 31.17/4.51    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f82])).
% 31.17/4.51  
% 31.17/4.51  fof(f23,axiom,(
% 31.17/4.51    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f45,plain,(
% 31.17/4.51    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 31.17/4.51    inference(ennf_transformation,[],[f23])).
% 31.17/4.51  
% 31.17/4.51  fof(f46,plain,(
% 31.17/4.51    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 31.17/4.51    inference(flattening,[],[f45])).
% 31.17/4.51  
% 31.17/4.51  fof(f130,plain,(
% 31.17/4.51    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f46])).
% 31.17/4.51  
% 31.17/4.51  fof(f20,axiom,(
% 31.17/4.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f39,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.17/4.51    inference(ennf_transformation,[],[f20])).
% 31.17/4.51  
% 31.17/4.51  fof(f40,plain,(
% 31.17/4.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.17/4.51    inference(flattening,[],[f39])).
% 31.17/4.51  
% 31.17/4.51  fof(f117,plain,(
% 31.17/4.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f40])).
% 31.17/4.51  
% 31.17/4.51  fof(f16,axiom,(
% 31.17/4.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f35,plain,(
% 31.17/4.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 31.17/4.51    inference(ennf_transformation,[],[f16])).
% 31.17/4.51  
% 31.17/4.51  fof(f36,plain,(
% 31.17/4.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.17/4.51    inference(flattening,[],[f35])).
% 31.17/4.51  
% 31.17/4.51  fof(f66,plain,(
% 31.17/4.51    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.17/4.51    inference(nnf_transformation,[],[f36])).
% 31.17/4.51  
% 31.17/4.51  fof(f111,plain,(
% 31.17/4.51    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f66])).
% 31.17/4.51  
% 31.17/4.51  fof(f17,axiom,(
% 31.17/4.51    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f114,plain,(
% 31.17/4.51    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 31.17/4.51    inference(cnf_transformation,[],[f17])).
% 31.17/4.51  
% 31.17/4.51  fof(f11,axiom,(
% 31.17/4.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f28,plain,(
% 31.17/4.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 31.17/4.51    inference(pure_predicate_removal,[],[f11])).
% 31.17/4.51  
% 31.17/4.51  fof(f30,plain,(
% 31.17/4.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.17/4.51    inference(ennf_transformation,[],[f28])).
% 31.17/4.51  
% 31.17/4.51  fof(f105,plain,(
% 31.17/4.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.17/4.51    inference(cnf_transformation,[],[f30])).
% 31.17/4.51  
% 31.17/4.51  fof(f10,axiom,(
% 31.17/4.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.17/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.17/4.51  
% 31.17/4.51  fof(f104,plain,(
% 31.17/4.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.17/4.51    inference(cnf_transformation,[],[f10])).
% 31.17/4.51  
% 31.17/4.51  fof(f98,plain,(
% 31.17/4.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 31.17/4.51    inference(cnf_transformation,[],[f64])).
% 31.17/4.51  
% 31.17/4.51  fof(f149,plain,(
% 31.17/4.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 31.17/4.51    inference(equality_resolution,[],[f98])).
% 31.17/4.51  
% 31.17/4.51  fof(f97,plain,(
% 31.17/4.51    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f64])).
% 31.17/4.51  
% 31.17/4.51  fof(f113,plain,(
% 31.17/4.51    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 31.17/4.51    inference(cnf_transformation,[],[f17])).
% 31.17/4.51  
% 31.17/4.51  cnf(c_56,negated_conjecture,
% 31.17/4.51      ( l1_pre_topc(sK6) ),
% 31.17/4.51      inference(cnf_transformation,[],[f139]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2155,plain,
% 31.17/4.51      ( l1_pre_topc(sK6) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_29,plain,
% 31.17/4.51      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 31.17/4.51      inference(cnf_transformation,[],[f116]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2182,plain,
% 31.17/4.51      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3528,plain,
% 31.17/4.51      ( l1_struct_0(sK6) = iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_2155,c_2182]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_28,plain,
% 31.17/4.51      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 31.17/4.51      inference(cnf_transformation,[],[f115]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2183,plain,
% 31.17/4.51      ( u1_struct_0(X0) = k2_struct_0(X0)
% 31.17/4.51      | l1_struct_0(X0) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3835,plain,
% 31.17/4.51      ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_3528,c_2183]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_54,negated_conjecture,
% 31.17/4.51      ( l1_pre_topc(sK7) ),
% 31.17/4.51      inference(cnf_transformation,[],[f141]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2157,plain,
% 31.17/4.51      ( l1_pre_topc(sK7) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3527,plain,
% 31.17/4.51      ( l1_struct_0(sK7) = iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_2157,c_2182]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3672,plain,
% 31.17/4.51      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_3527,c_2183]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_51,negated_conjecture,
% 31.17/4.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 31.17/4.51      inference(cnf_transformation,[],[f144]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2160,plain,
% 31.17/4.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3837,plain,
% 31.17/4.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_struct_0(sK7)))) = iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_3672,c_2160]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_4161,plain,
% 31.17/4.51      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)))) = iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_3835,c_3837]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_41,plain,
% 31.17/4.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 31.17/4.51      | v5_pre_topc(X0,X1,X2)
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 31.17/4.51      | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 31.17/4.51      | ~ v1_funct_1(X0)
% 31.17/4.51      | ~ v2_pre_topc(X1)
% 31.17/4.51      | ~ v2_pre_topc(X2)
% 31.17/4.51      | ~ l1_pre_topc(X1)
% 31.17/4.51      | ~ l1_pre_topc(X2) ),
% 31.17/4.51      inference(cnf_transformation,[],[f128]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2170,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,X2) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 31.17/4.51      | m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | v2_pre_topc(X2) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(X2) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_8999,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | m1_subset_1(sK3(X1,sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK7) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK7) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_3672,c_2170]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9009,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | m1_subset_1(sK3(X1,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK7) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK7) != iProver_top ),
% 31.17/4.51      inference(light_normalisation,[status(thm)],[c_8999,c_3672]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_55,negated_conjecture,
% 31.17/4.51      ( v2_pre_topc(sK7) ),
% 31.17/4.51      inference(cnf_transformation,[],[f140]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_62,plain,
% 31.17/4.51      ( v2_pre_topc(sK7) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_63,plain,
% 31.17/4.51      ( l1_pre_topc(sK7) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9586,plain,
% 31.17/4.51      ( l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | m1_subset_1(sK3(X1,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_9009,c_62,c_63]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9587,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | m1_subset_1(sK3(X1,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top ),
% 31.17/4.51      inference(renaming,[status(thm)],[c_9586]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9601,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(sK6),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,sK6,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | m1_subset_1(sK3(sK6,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK6) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK6) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_3835,c_9587]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9625,plain,
% 31.17/4.51      ( v1_funct_2(X0,k2_struct_0(sK6),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,sK6,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | m1_subset_1(sK3(sK6,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK6) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK6) != iProver_top ),
% 31.17/4.51      inference(light_normalisation,[status(thm)],[c_9601,c_3835]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_58,negated_conjecture,
% 31.17/4.51      ( v2_pre_topc(sK6) ),
% 31.17/4.51      inference(cnf_transformation,[],[f137]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_59,plain,
% 31.17/4.51      ( v2_pre_topc(sK6) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_61,plain,
% 31.17/4.51      ( l1_pre_topc(sK6) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_10049,plain,
% 31.17/4.51      ( v1_funct_2(X0,k2_struct_0(sK6),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,sK6,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | m1_subset_1(sK3(sK6,sK7,X0),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_9625,c_59,c_61]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_10062,plain,
% 31.17/4.51      ( v1_funct_2(sK8,k2_struct_0(sK6),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(sK8,sK6,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top
% 31.17/4.51      | v1_funct_1(sK8) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_4161,c_10049]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_53,negated_conjecture,
% 31.17/4.51      ( v1_funct_1(sK8) ),
% 31.17/4.51      inference(cnf_transformation,[],[f142]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_64,plain,
% 31.17/4.51      ( v1_funct_1(sK8) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_50,negated_conjecture,
% 31.17/4.51      ( ~ v5_pre_topc(sK8,sK6,sK7) ),
% 31.17/4.51      inference(cnf_transformation,[],[f145]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_67,plain,
% 31.17/4.51      ( v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_52,negated_conjecture,
% 31.17/4.51      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 31.17/4.51      inference(cnf_transformation,[],[f143]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2159,plain,
% 31.17/4.51      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3838,plain,
% 31.17/4.51      ( v1_funct_2(sK8,u1_struct_0(sK6),k2_struct_0(sK7)) = iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_3672,c_2159]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_4162,plain,
% 31.17/4.51      ( v1_funct_2(sK8,k2_struct_0(sK6),k2_struct_0(sK7)) = iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_3835,c_3838]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_10309,plain,
% 31.17/4.51      ( m1_subset_1(sK3(sK6,sK7,sK8),k1_zfmisc_1(k2_struct_0(sK7))) = iProver_top ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_10062,c_64,c_67,c_4162]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_16,plain,
% 31.17/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.17/4.51      inference(cnf_transformation,[],[f102]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2195,plain,
% 31.17/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.17/4.51      | r1_tarski(X0,X1) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_10314,plain,
% 31.17/4.51      ( r1_tarski(sK3(sK6,sK7,sK8),k2_struct_0(sK7)) = iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_10309,c_2195]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_39,plain,
% 31.17/4.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 31.17/4.51      | ~ v5_pre_topc(X0,X1,X2)
% 31.17/4.51      | ~ v3_pre_topc(X3,X2)
% 31.17/4.51      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 31.17/4.51      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 31.17/4.51      | ~ v1_funct_1(X0)
% 31.17/4.51      | ~ l1_pre_topc(X1)
% 31.17/4.51      | ~ l1_pre_topc(X2)
% 31.17/4.51      | k2_struct_0(X2) = k1_xboole_0 ),
% 31.17/4.51      inference(cnf_transformation,[],[f119]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2172,plain,
% 31.17/4.51      ( k2_struct_0(X0) = k1_xboole_0
% 31.17/4.51      | v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X1,X2,X0) != iProver_top
% 31.17/4.51      | v3_pre_topc(X3,X0) != iProver_top
% 31.17/4.51      | v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X0),X1,X3),X2) = iProver_top
% 31.17/4.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
% 31.17/4.51      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.17/4.51      | v1_funct_1(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(X2) != iProver_top
% 31.17/4.51      | l1_pre_topc(X0) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_12670,plain,
% 31.17/4.51      ( k2_struct_0(sK7) = k1_xboole_0
% 31.17/4.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) != iProver_top
% 31.17/4.51      | v3_pre_topc(X2,sK7) != iProver_top
% 31.17/4.51      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,X2),X1) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK7) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_3672,c_2172]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_12681,plain,
% 31.17/4.51      ( k2_struct_0(sK7) = k1_xboole_0
% 31.17/4.51      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) != iProver_top
% 31.17/4.51      | v3_pre_topc(X2,sK7) != iProver_top
% 31.17/4.51      | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,X2),X1) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK7))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK7) != iProver_top ),
% 31.17/4.51      inference(light_normalisation,[status(thm)],[c_12670,c_3672]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_57,negated_conjecture,
% 31.17/4.51      ( v1_tdlat_3(sK6) ),
% 31.17/4.51      inference(cnf_transformation,[],[f138]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_46,plain,
% 31.17/4.51      ( v3_pre_topc(X0,X1)
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.17/4.51      | ~ v1_tdlat_3(X1)
% 31.17/4.51      | ~ v2_pre_topc(X1)
% 31.17/4.51      | ~ l1_pre_topc(X1) ),
% 31.17/4.51      inference(cnf_transformation,[],[f131]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2878,plain,
% 31.17/4.51      ( v3_pre_topc(X0,sK6)
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 31.17/4.51      | ~ v1_tdlat_3(sK6)
% 31.17/4.51      | ~ v2_pre_topc(sK6)
% 31.17/4.51      | ~ l1_pre_topc(sK6) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_46]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3221,plain,
% 31.17/4.51      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),sK6)
% 31.17/4.51      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 31.17/4.51      | ~ v1_tdlat_3(sK6)
% 31.17/4.51      | ~ v2_pre_topc(sK6)
% 31.17/4.51      | ~ l1_pre_topc(sK6) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_2878]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3783,plain,
% 31.17/4.51      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
% 31.17/4.51      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
% 31.17/4.51      | ~ v1_tdlat_3(sK6)
% 31.17/4.51      | ~ v2_pre_topc(sK6)
% 31.17/4.51      | ~ l1_pre_topc(sK6) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_3221]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_33,plain,
% 31.17/4.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 31.17/4.51      | v5_pre_topc(X0,X1,X2)
% 31.17/4.51      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK2(X1,X2,X0)),X1)
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 31.17/4.51      | ~ v1_funct_1(X0)
% 31.17/4.51      | ~ l1_pre_topc(X1)
% 31.17/4.51      | ~ l1_pre_topc(X2)
% 31.17/4.51      | k2_struct_0(X2) = k1_xboole_0 ),
% 31.17/4.51      inference(cnf_transformation,[],[f125]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3784,plain,
% 31.17/4.51      ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
% 31.17/4.51      | v5_pre_topc(sK8,sK6,sK7)
% 31.17/4.51      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),sK6)
% 31.17/4.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 31.17/4.51      | ~ v1_funct_1(sK8)
% 31.17/4.51      | ~ l1_pre_topc(sK7)
% 31.17/4.51      | ~ l1_pre_topc(sK6)
% 31.17/4.51      | k2_struct_0(sK7) = k1_xboole_0 ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_33]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_20,plain,
% 31.17/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.17/4.51      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 31.17/4.51      inference(cnf_transformation,[],[f107]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2896,plain,
% 31.17/4.51      ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 31.17/4.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_20]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_5017,plain,
% 31.17/4.51      ( m1_subset_1(k8_relset_1(u1_struct_0(sK6),u1_struct_0(sK7),sK8,sK2(sK6,sK7,sK8)),k1_zfmisc_1(u1_struct_0(sK6)))
% 31.17/4.51      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_2896]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_13768,plain,
% 31.17/4.51      ( k2_struct_0(sK7) = k1_xboole_0 ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_12681,c_58,c_57,c_56,c_54,c_53,c_52,c_51,c_50,c_3783,
% 31.17/4.51                 c_3784,c_5017]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3,plain,
% 31.17/4.51      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 31.17/4.51      inference(cnf_transformation,[],[f90]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2203,plain,
% 31.17/4.51      ( r1_tarski(X0,X1) = iProver_top
% 31.17/4.51      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_1,plain,
% 31.17/4.51      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 31.17/4.51      inference(cnf_transformation,[],[f87]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2205,plain,
% 31.17/4.51      ( r2_hidden(X0,X1) != iProver_top
% 31.17/4.51      | v1_xboole_0(X1) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_4981,plain,
% 31.17/4.51      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_2203,c_2205]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_4596,plain,
% 31.17/4.51      ( r1_tarski(sK8,k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7))) = iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_4161,c_2195]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_6,plain,
% 31.17/4.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 31.17/4.51      inference(cnf_transformation,[],[f95]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2200,plain,
% 31.17/4.51      ( X0 = X1
% 31.17/4.51      | r1_tarski(X1,X0) != iProver_top
% 31.17/4.51      | r1_tarski(X0,X1) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_6071,plain,
% 31.17/4.51      ( k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)) = sK8
% 31.17/4.51      | r1_tarski(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)),sK8) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_4596,c_2200]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_6322,plain,
% 31.17/4.51      ( k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7)) = sK8
% 31.17/4.51      | v1_xboole_0(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK7))) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_4981,c_6071]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_13793,plain,
% 31.17/4.51      ( k2_zfmisc_1(k2_struct_0(sK6),k1_xboole_0) = sK8
% 31.17/4.51      | v1_xboole_0(k2_zfmisc_1(k2_struct_0(sK6),k1_xboole_0)) != iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_13768,c_6322]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_10,plain,
% 31.17/4.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 31.17/4.51      inference(cnf_transformation,[],[f148]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_13839,plain,
% 31.17/4.51      ( sK8 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_13793,c_10]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_5,plain,
% 31.17/4.51      ( v1_xboole_0(k1_xboole_0) ),
% 31.17/4.51      inference(cnf_transformation,[],[f92]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_185,plain,
% 31.17/4.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3903,plain,
% 31.17/4.51      ( r1_tarski(sK8,X0) | r2_hidden(sK1(sK8,X0),sK8) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_3]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3909,plain,
% 31.17/4.51      ( r1_tarski(sK8,X0) = iProver_top
% 31.17/4.51      | r2_hidden(sK1(sK8,X0),sK8) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_3903]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3911,plain,
% 31.17/4.51      ( r1_tarski(sK8,k1_xboole_0) = iProver_top
% 31.17/4.51      | r2_hidden(sK1(sK8,k1_xboole_0),sK8) = iProver_top ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_3909]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3934,plain,
% 31.17/4.51      ( ~ r1_tarski(X0,sK8) | ~ r1_tarski(sK8,X0) | sK8 = X0 ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_6]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3935,plain,
% 31.17/4.51      ( sK8 = X0
% 31.17/4.51      | r1_tarski(X0,sK8) != iProver_top
% 31.17/4.51      | r1_tarski(sK8,X0) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_3934]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3937,plain,
% 31.17/4.51      ( sK8 = k1_xboole_0
% 31.17/4.51      | r1_tarski(sK8,k1_xboole_0) != iProver_top
% 31.17/4.51      | r1_tarski(k1_xboole_0,sK8) != iProver_top ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_3935]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9,plain,
% 31.17/4.51      ( r1_tarski(k1_xboole_0,X0) ),
% 31.17/4.51      inference(cnf_transformation,[],[f96]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_5332,plain,
% 31.17/4.51      ( r1_tarski(k1_xboole_0,sK8) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_9]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_5335,plain,
% 31.17/4.51      ( r1_tarski(k1_xboole_0,sK8) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_5332]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9848,plain,
% 31.17/4.51      ( ~ r2_hidden(sK1(sK8,X0),sK8) | ~ v1_xboole_0(sK8) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_1]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9849,plain,
% 31.17/4.51      ( r2_hidden(sK1(sK8,X0),sK8) != iProver_top
% 31.17/4.51      | v1_xboole_0(sK8) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_9848]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9851,plain,
% 31.17/4.51      ( r2_hidden(sK1(sK8,k1_xboole_0),sK8) != iProver_top
% 31.17/4.51      | v1_xboole_0(sK8) != iProver_top ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_9849]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_19,plain,
% 31.17/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.17/4.51      | ~ v1_xboole_0(X2)
% 31.17/4.51      | v1_xboole_0(X0) ),
% 31.17/4.51      inference(cnf_transformation,[],[f106]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2192,plain,
% 31.17/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.17/4.51      | v1_xboole_0(X2) != iProver_top
% 31.17/4.51      | v1_xboole_0(X0) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_11310,plain,
% 31.17/4.51      ( v1_xboole_0(k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v1_xboole_0(sK8) = iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_4161,c_2192]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_13777,plain,
% 31.17/4.51      ( v1_xboole_0(sK8) = iProver_top
% 31.17/4.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_13768,c_11310]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_15422,plain,
% 31.17/4.51      ( sK8 = k1_xboole_0 ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_13839,c_185,c_3911,c_3937,c_5335,c_9851,c_13777]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_16507,plain,
% 31.17/4.51      ( r1_tarski(sK3(sK6,sK7,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(light_normalisation,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_10314,c_13768,c_15422]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_16511,plain,
% 31.17/4.51      ( sK3(sK6,sK7,k1_xboole_0) = k1_xboole_0
% 31.17/4.51      | r1_tarski(k1_xboole_0,sK3(sK6,sK7,k1_xboole_0)) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_16507,c_2200]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2198,plain,
% 31.17/4.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_106220,plain,
% 31.17/4.51      ( sK3(sK6,sK7,k1_xboole_0) = k1_xboole_0 ),
% 31.17/4.51      inference(forward_subsumption_resolution,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_16511,c_2198]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_13803,plain,
% 31.17/4.51      ( u1_struct_0(sK7) = k1_xboole_0 ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_13768,c_3672]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_40,plain,
% 31.17/4.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 31.17/4.51      | v5_pre_topc(X0,X1,X2)
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 31.17/4.51      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0))))
% 31.17/4.51      | ~ v1_funct_1(X0)
% 31.17/4.51      | ~ v2_pre_topc(X1)
% 31.17/4.51      | ~ v2_pre_topc(X2)
% 31.17/4.51      | ~ l1_pre_topc(X1)
% 31.17/4.51      | ~ l1_pre_topc(X2) ),
% 31.17/4.51      inference(cnf_transformation,[],[f129]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2171,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,X2) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK3(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK3(X1,X2,X0)))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | v2_pre_topc(X2) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(X2) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_14508,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK7) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK7) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_13803,c_2171]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_14564,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK7) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK7) != iProver_top ),
% 31.17/4.51      inference(light_normalisation,[status(thm)],[c_14508,c_13803]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_14565,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK7) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK7) != iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_14564,c_10]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_177,plain,
% 31.17/4.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_943,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_4147,plain,
% 31.17/4.51      ( X0 != X1 | k2_struct_0(X2) != X1 | k2_struct_0(X2) = X0 ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_943]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_6675,plain,
% 31.17/4.51      ( X0 != k1_xboole_0
% 31.17/4.51      | k2_struct_0(sK7) = X0
% 31.17/4.51      | k2_struct_0(sK7) != k1_xboole_0 ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_4147]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_7540,plain,
% 31.17/4.51      ( k2_struct_0(sK7) = sK8
% 31.17/4.51      | k2_struct_0(sK7) != k1_xboole_0
% 31.17/4.51      | sK8 != k1_xboole_0 ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_6675]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_962,plain,
% 31.17/4.51      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 31.17/4.51      theory(equality) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2804,plain,
% 31.17/4.51      ( v1_funct_1(X0) | ~ v1_funct_1(sK8) | X0 != sK8 ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_962]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_7542,plain,
% 31.17/4.51      ( v1_funct_1(k2_struct_0(sK7))
% 31.17/4.51      | ~ v1_funct_1(sK8)
% 31.17/4.51      | k2_struct_0(sK7) != sK8 ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_2804]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_7543,plain,
% 31.17/4.51      ( k2_struct_0(sK7) != sK8
% 31.17/4.51      | v1_funct_1(k2_struct_0(sK7)) = iProver_top
% 31.17/4.51      | v1_funct_1(sK8) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_7542]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_10788,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK7) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK7) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_3672,c_2171]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_10798,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK7) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK7) != iProver_top ),
% 31.17/4.51      inference(light_normalisation,[status(thm)],[c_10788,c_3672]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_11691,plain,
% 31.17/4.51      ( l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_10798,c_62,c_63]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_11692,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK7)))) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k2_struct_0(sK7),X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top ),
% 31.17/4.51      inference(renaming,[status(thm)],[c_11691]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_13776,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_13768,c_11692]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_14002,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_13776,c_10]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_35,plain,
% 31.17/4.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 31.17/4.51      | v5_pre_topc(X0,X1,X2)
% 31.17/4.51      | v3_pre_topc(sK2(X1,X2,X0),X2)
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 31.17/4.51      | ~ v1_funct_1(X0)
% 31.17/4.51      | ~ l1_pre_topc(X1)
% 31.17/4.51      | ~ l1_pre_topc(X2)
% 31.17/4.51      | k2_struct_0(X2) = k1_xboole_0 ),
% 31.17/4.51      inference(cnf_transformation,[],[f123]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_14167,plain,
% 31.17/4.51      ( ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
% 31.17/4.51      | v5_pre_topc(sK8,sK6,sK7)
% 31.17/4.51      | v3_pre_topc(sK2(sK6,sK7,sK8),sK7)
% 31.17/4.51      | ~ v1_funct_1(sK8)
% 31.17/4.51      | ~ l1_pre_topc(sK7)
% 31.17/4.51      | ~ l1_pre_topc(sK6)
% 31.17/4.51      | k2_struct_0(sK7) = k1_xboole_0 ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_35,c_51]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_14178,plain,
% 31.17/4.51      ( k2_struct_0(sK7) = k1_xboole_0 ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_14167,c_58,c_57,c_56,c_54,c_53,c_52,c_51,c_50,c_3783,
% 31.17/4.51                 c_3784,c_5017]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_946,plain,
% 31.17/4.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.17/4.51      theory(equality) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_14209,plain,
% 31.17/4.51      ( r1_tarski(X0,k2_struct_0(sK7))
% 31.17/4.51      | ~ r1_tarski(X1,k1_xboole_0)
% 31.17/4.51      | X0 != X1 ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_14178,c_946]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_942,plain,( X0 = X0 ),theory(equality) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_16946,plain,
% 31.17/4.51      ( r1_tarski(X0,k2_struct_0(sK7)) | ~ r1_tarski(X0,k1_xboole_0) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_14209,c_942]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_5251,plain,
% 31.17/4.51      ( ~ r1_tarski(X0,X1)
% 31.17/4.51      | ~ r1_tarski(X1,X0)
% 31.17/4.51      | ~ v1_funct_1(X0)
% 31.17/4.51      | v1_funct_1(X1) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_6,c_962]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_18147,plain,
% 31.17/4.51      ( ~ r1_tarski(X0,k1_xboole_0)
% 31.17/4.51      | ~ r1_tarski(k2_struct_0(sK7),X0)
% 31.17/4.51      | v1_funct_1(X0)
% 31.17/4.51      | ~ v1_funct_1(k2_struct_0(sK7)) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_16946,c_5251]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_18152,plain,
% 31.17/4.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 31.17/4.51      | r1_tarski(k2_struct_0(sK7),X0) != iProver_top
% 31.17/4.51      | v1_funct_1(X0) = iProver_top
% 31.17/4.51      | v1_funct_1(k2_struct_0(sK7)) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_18147]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_949,plain,
% 31.17/4.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.17/4.51      theory(equality) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9803,plain,
% 31.17/4.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_949,c_942]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_14202,plain,
% 31.17/4.51      ( m1_subset_1(k2_struct_0(sK7),X0)
% 31.17/4.51      | ~ m1_subset_1(k1_xboole_0,X0) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_14178,c_9803]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_15461,plain,
% 31.17/4.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 31.17/4.51      | r1_tarski(k2_struct_0(sK7),X0) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_14202,c_16]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_15,plain,
% 31.17/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.17/4.51      inference(cnf_transformation,[],[f103]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_18319,plain,
% 31.17/4.51      ( r1_tarski(k2_struct_0(sK7),X0) | ~ r1_tarski(k1_xboole_0,X0) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_15461,c_15]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_18320,plain,
% 31.17/4.51      ( r1_tarski(k2_struct_0(sK7),X0) = iProver_top
% 31.17/4.51      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_18319]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_8095,plain,
% 31.17/4.51      ( X0 != X1 | X1 = X0 ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_943,c_942]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_21012,plain,
% 31.17/4.51      ( k1_xboole_0 = k2_struct_0(sK7) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_8095,c_14178]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_21047,plain,
% 31.17/4.51      ( ~ r1_tarski(X0,k2_struct_0(sK7))
% 31.17/4.51      | r1_tarski(X1,k1_xboole_0)
% 31.17/4.51      | X1 != X0 ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_21012,c_946]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_24041,plain,
% 31.17/4.51      ( ~ r1_tarski(X0,k2_struct_0(sK7)) | r1_tarski(X0,k1_xboole_0) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_21047,c_942]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_24042,plain,
% 31.17/4.51      ( r1_tarski(X0,k2_struct_0(sK7)) != iProver_top
% 31.17/4.51      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_24041]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_948,plain,
% 31.17/4.51      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 31.17/4.51      theory(equality) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9805,plain,
% 31.17/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.17/4.51      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 31.17/4.51      | X2 != X0
% 31.17/4.51      | X3 != X1 ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_949,c_948]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_48932,plain,
% 31.17/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK7)))
% 31.17/4.51      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
% 31.17/4.51      | X0 != X1 ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_9805,c_14178]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_49782,plain,
% 31.17/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK7)))
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_48932,c_942]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_50359,plain,
% 31.17/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 31.17/4.51      | r1_tarski(X0,k2_struct_0(sK7)) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_49782,c_16]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_50360,plain,
% 31.17/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | r1_tarski(X0,k2_struct_0(sK7)) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_50359]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_52030,plain,
% 31.17/4.51      ( l1_pre_topc(X1) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_14565,c_58,c_57,c_56,c_54,c_53,c_64,c_52,c_51,c_50,
% 31.17/4.51                 c_177,c_185,c_3783,c_3784,c_3911,c_3937,c_5017,c_5335,
% 31.17/4.51                 c_7540,c_7543,c_9851,c_13777,c_14002,c_18152,c_18320,
% 31.17/4.51                 c_24042,c_50360]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_52031,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,X1,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,sK3(X1,sK7,X0))),k8_relset_1(u1_struct_0(X1),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(X1,sK7,X0)))) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top ),
% 31.17/4.51      inference(renaming,[status(thm)],[c_52030]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_52046,plain,
% 31.17/4.51      ( v1_funct_2(X0,u1_struct_0(sK6),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,sK6,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(sK6,k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,sK3(sK6,sK7,X0))),k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(sK6,sK7,X0)))) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK6) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK6) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_3835,c_52031]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_52067,plain,
% 31.17/4.51      ( v1_funct_2(X0,k2_struct_0(sK6),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,sK6,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(sK6,k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,sK3(sK6,sK7,X0))),k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(sK6,sK7,X0)))) != iProver_top
% 31.17/4.51      | v2_pre_topc(sK6) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK6) != iProver_top ),
% 31.17/4.51      inference(light_normalisation,[status(thm)],[c_52046,c_3835]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_52659,plain,
% 31.17/4.51      ( v1_funct_2(X0,k2_struct_0(sK6),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,sK6,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | r1_tarski(k2_pre_topc(sK6,k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,sK3(sK6,sK7,X0))),k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,k2_pre_topc(sK7,sK3(sK6,sK7,X0)))) != iProver_top ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_52067,c_59,c_61]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_52669,plain,
% 31.17/4.51      ( v1_funct_2(X0,k2_struct_0(sK6),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(X0,sK6,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | v1_xboole_0(k2_pre_topc(sK6,k8_relset_1(k2_struct_0(sK6),k1_xboole_0,X0,sK3(sK6,sK7,X0)))) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_4981,c_52659]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_106243,plain,
% 31.17/4.51      ( v1_funct_2(k1_xboole_0,k2_struct_0(sK6),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | v1_xboole_0(k2_pre_topc(sK6,k8_relset_1(k2_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_106220,c_52669]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_22,plain,
% 31.17/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.17/4.51      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 31.17/4.51      inference(cnf_transformation,[],[f110]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2189,plain,
% 31.17/4.51      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 31.17/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9267,plain,
% 31.17/4.51      ( k8_relset_1(k2_struct_0(sK6),k2_struct_0(sK7),sK8,k2_struct_0(sK7)) = k1_relset_1(k2_struct_0(sK6),k2_struct_0(sK7),sK8) ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_4161,c_2189]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_21,plain,
% 31.17/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.17/4.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 31.17/4.51      inference(cnf_transformation,[],[f108]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2190,plain,
% 31.17/4.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 31.17/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_5816,plain,
% 31.17/4.51      ( k1_relset_1(k2_struct_0(sK6),k2_struct_0(sK7),sK8) = k1_relat_1(sK8) ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_4161,c_2190]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9279,plain,
% 31.17/4.51      ( k8_relset_1(k2_struct_0(sK6),k2_struct_0(sK7),sK8,k2_struct_0(sK7)) = k1_relat_1(sK8) ),
% 31.17/4.51      inference(light_normalisation,[status(thm)],[c_9267,c_5816]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_17742,plain,
% 31.17/4.51      ( k8_relset_1(k2_struct_0(sK6),k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 31.17/4.51      inference(light_normalisation,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_9279,c_13768,c_15422]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2191,plain,
% 31.17/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.17/4.51      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_17744,plain,
% 31.17/4.51      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top
% 31.17/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k1_xboole_0))) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_17742,c_2191]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_17745,plain,
% 31.17/4.51      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top
% 31.17/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_17744,c_10]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_168,plain,
% 31.17/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.17/4.51      | r1_tarski(X0,X1) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_170,plain,
% 31.17/4.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 31.17/4.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_168]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_179,plain,
% 31.17/4.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_177]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_17921,plain,
% 31.17/4.51      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) = iProver_top ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_17745,c_170,c_179]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_49,plain,
% 31.17/4.51      ( v4_pre_topc(X0,X1)
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.17/4.51      | ~ v1_tdlat_3(X1)
% 31.17/4.51      | ~ v2_pre_topc(X1)
% 31.17/4.51      | ~ l1_pre_topc(X1) ),
% 31.17/4.51      inference(cnf_transformation,[],[f134]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2162,plain,
% 31.17/4.51      ( v4_pre_topc(X0,X1) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.17/4.51      | v1_tdlat_3(X1) != iProver_top
% 31.17/4.51      | v2_pre_topc(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_43,plain,
% 31.17/4.51      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 31.17/4.51      inference(cnf_transformation,[],[f130]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2168,plain,
% 31.17/4.51      ( v1_tdlat_3(X0) != iProver_top
% 31.17/4.51      | v2_pre_topc(X0) = iProver_top
% 31.17/4.51      | l1_pre_topc(X0) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2387,plain,
% 31.17/4.51      ( v4_pre_topc(X0,X1) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 31.17/4.51      | v1_tdlat_3(X1) != iProver_top
% 31.17/4.51      | l1_pre_topc(X1) != iProver_top ),
% 31.17/4.51      inference(forward_subsumption_resolution,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_2162,c_2168]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_27482,plain,
% 31.17/4.51      ( v4_pre_topc(X0,sK6) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
% 31.17/4.51      | v1_tdlat_3(sK6) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK6) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_3835,c_2387]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_60,plain,
% 31.17/4.51      ( v1_tdlat_3(sK6) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_28056,plain,
% 31.17/4.51      ( v4_pre_topc(X0,sK6) = iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_27482,c_60,c_61]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_28069,plain,
% 31.17/4.51      ( v4_pre_topc(k1_relat_1(k1_xboole_0),sK6) = iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_17921,c_28056]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_31,plain,
% 31.17/4.51      ( ~ v4_pre_topc(X0,X1)
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.17/4.51      | ~ l1_pre_topc(X1)
% 31.17/4.51      | k2_pre_topc(X1,X0) = X0 ),
% 31.17/4.51      inference(cnf_transformation,[],[f117]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2180,plain,
% 31.17/4.51      ( k2_pre_topc(X0,X1) = X1
% 31.17/4.51      | v4_pre_topc(X1,X0) != iProver_top
% 31.17/4.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 31.17/4.51      | l1_pre_topc(X0) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_18035,plain,
% 31.17/4.51      ( k2_pre_topc(sK6,X0) = X0
% 31.17/4.51      | v4_pre_topc(X0,sK6) != iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
% 31.17/4.51      | l1_pre_topc(sK6) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_3835,c_2180]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_18266,plain,
% 31.17/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top
% 31.17/4.51      | v4_pre_topc(X0,sK6) != iProver_top
% 31.17/4.51      | k2_pre_topc(sK6,X0) = X0 ),
% 31.17/4.51      inference(global_propositional_subsumption,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_18035,c_61]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_18267,plain,
% 31.17/4.51      ( k2_pre_topc(sK6,X0) = X0
% 31.17/4.51      | v4_pre_topc(X0,sK6) != iProver_top
% 31.17/4.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) != iProver_top ),
% 31.17/4.51      inference(renaming,[status(thm)],[c_18266]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_18278,plain,
% 31.17/4.51      ( k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0)
% 31.17/4.51      | v4_pre_topc(k1_relat_1(k1_xboole_0),sK6) != iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_17921,c_18267]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_28341,plain,
% 31.17/4.51      ( k2_pre_topc(sK6,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_28069,c_18278]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_106284,plain,
% 31.17/4.51      ( v1_funct_2(k1_xboole_0,k2_struct_0(sK6),k1_xboole_0) != iProver_top
% 31.17/4.51      | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
% 31.17/4.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 31.17/4.51      | v1_xboole_0(k1_relat_1(k1_xboole_0)) != iProver_top ),
% 31.17/4.51      inference(light_normalisation,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_106243,c_17742,c_28341]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2161,plain,
% 31.17/4.51      ( v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_15429,plain,
% 31.17/4.51      ( v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_15422,c_2161]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_13802,plain,
% 31.17/4.51      ( v1_funct_2(sK8,k2_struct_0(sK6),k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_13768,c_4162]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_15427,plain,
% 31.17/4.51      ( v1_funct_2(k1_xboole_0,k2_struct_0(sK6),k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(demodulation,[status(thm)],[c_15422,c_13802]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_25,plain,
% 31.17/4.51      ( ~ v1_partfun1(X0,X1)
% 31.17/4.51      | ~ v4_relat_1(X0,X1)
% 31.17/4.51      | ~ v1_relat_1(X0)
% 31.17/4.51      | k1_relat_1(X0) = X1 ),
% 31.17/4.51      inference(cnf_transformation,[],[f111]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_944,plain,
% 31.17/4.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 31.17/4.51      theory(equality) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9685,plain,
% 31.17/4.51      ( ~ v1_partfun1(X0,X1)
% 31.17/4.51      | ~ v4_relat_1(X0,X1)
% 31.17/4.51      | ~ v1_relat_1(X0)
% 31.17/4.51      | ~ v1_xboole_0(X1)
% 31.17/4.51      | v1_xboole_0(k1_relat_1(X0)) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_25,c_944]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9690,plain,
% 31.17/4.51      ( v1_partfun1(X0,X1) != iProver_top
% 31.17/4.51      | v4_relat_1(X0,X1) != iProver_top
% 31.17/4.51      | v1_relat_1(X0) != iProver_top
% 31.17/4.51      | v1_xboole_0(X1) != iProver_top
% 31.17/4.51      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_9685]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_9692,plain,
% 31.17/4.51      ( v1_partfun1(k1_xboole_0,k1_xboole_0) != iProver_top
% 31.17/4.51      | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
% 31.17/4.51      | v1_relat_1(k1_xboole_0) != iProver_top
% 31.17/4.51      | v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top
% 31.17/4.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_9690]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_6745,plain,
% 31.17/4.51      ( r1_tarski(k1_xboole_0,k6_partfun1(X0)) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_9]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_6749,plain,
% 31.17/4.51      ( r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_6745]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_26,plain,
% 31.17/4.51      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 31.17/4.51      inference(cnf_transformation,[],[f114]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2185,plain,
% 31.17/4.51      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3422,plain,
% 31.17/4.51      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_10,c_2185]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_4595,plain,
% 31.17/4.51      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_3422,c_2195]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_4615,plain,
% 31.17/4.51      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
% 31.17/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_4595]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_4226,plain,
% 31.17/4.51      ( ~ r1_tarski(X0,k6_partfun1(X1))
% 31.17/4.51      | ~ r1_tarski(k6_partfun1(X1),X0)
% 31.17/4.51      | X0 = k6_partfun1(X1) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_6]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_4228,plain,
% 31.17/4.51      ( ~ r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)
% 31.17/4.51      | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))
% 31.17/4.51      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_4226]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_18,plain,
% 31.17/4.51      ( v4_relat_1(X0,X1)
% 31.17/4.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.17/4.51      inference(cnf_transformation,[],[f105]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3127,plain,
% 31.17/4.51      ( v4_relat_1(X0,X1) | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_18,c_15]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3274,plain,
% 31.17/4.51      ( v4_relat_1(k1_xboole_0,X0) ),
% 31.17/4.51      inference(resolution,[status(thm)],[c_3127,c_9]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3275,plain,
% 31.17/4.51      ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_3274]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3277,plain,
% 31.17/4.51      ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_3275]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_17,plain,
% 31.17/4.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.17/4.51      inference(cnf_transformation,[],[f104]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_2194,plain,
% 31.17/4.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3108,plain,
% 31.17/4.51      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(superposition,[status(thm)],[c_10,c_2194]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_953,plain,
% 31.17/4.51      ( ~ v1_partfun1(X0,X1) | v1_partfun1(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.17/4.51      theory(equality) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3057,plain,
% 31.17/4.51      ( v1_partfun1(X0,X1)
% 31.17/4.51      | ~ v1_partfun1(k6_partfun1(X2),X2)
% 31.17/4.51      | X1 != X2
% 31.17/4.51      | X0 != k6_partfun1(X2) ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_953]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3058,plain,
% 31.17/4.51      ( X0 != X1
% 31.17/4.51      | X2 != k6_partfun1(X1)
% 31.17/4.51      | v1_partfun1(X2,X0) = iProver_top
% 31.17/4.51      | v1_partfun1(k6_partfun1(X1),X1) != iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_3057]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_3060,plain,
% 31.17/4.51      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 31.17/4.51      | k1_xboole_0 != k1_xboole_0
% 31.17/4.51      | v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) != iProver_top
% 31.17/4.51      | v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_3058]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_11,plain,
% 31.17/4.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.17/4.51      inference(cnf_transformation,[],[f149]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_176,plain,
% 31.17/4.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_11]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_12,plain,
% 31.17/4.51      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 31.17/4.51      | k1_xboole_0 = X1
% 31.17/4.51      | k1_xboole_0 = X0 ),
% 31.17/4.51      inference(cnf_transformation,[],[f97]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_175,plain,
% 31.17/4.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 31.17/4.51      | k1_xboole_0 = k1_xboole_0 ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_12]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_27,plain,
% 31.17/4.51      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 31.17/4.51      inference(cnf_transformation,[],[f113]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_134,plain,
% 31.17/4.51      ( v1_partfun1(k6_partfun1(X0),X0) = iProver_top ),
% 31.17/4.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(c_136,plain,
% 31.17/4.51      ( v1_partfun1(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 31.17/4.51      inference(instantiation,[status(thm)],[c_134]) ).
% 31.17/4.51  
% 31.17/4.51  cnf(contradiction,plain,
% 31.17/4.51      ( $false ),
% 31.17/4.51      inference(minisat,
% 31.17/4.51                [status(thm)],
% 31.17/4.51                [c_106284,c_15429,c_15427,c_9692,c_6749,c_4615,c_4228,
% 31.17/4.51                 c_3277,c_3108,c_3060,c_185,c_179,c_176,c_175,c_170,
% 31.17/4.51                 c_136]) ).
% 31.17/4.51  
% 31.17/4.51  
% 31.17/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.17/4.51  
% 31.17/4.51  ------                               Statistics
% 31.17/4.51  
% 31.17/4.51  ------ Selected
% 31.17/4.51  
% 31.17/4.51  total_time:                             3.706
% 31.17/4.51  
%------------------------------------------------------------------------------
