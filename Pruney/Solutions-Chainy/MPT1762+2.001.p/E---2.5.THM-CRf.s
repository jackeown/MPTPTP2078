%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:34 EST 2020

% Result     : Theorem 0.66s
% Output     : CNFRefutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  115 (2473 expanded)
%              Number of clauses        :   80 ( 775 expanded)
%              Number of leaves         :   17 ( 604 expanded)
%              Depth                    :   17
%              Number of atoms          :  470 (34405 expanded)
%              Number of equality atoms :   32 (1645 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => ( ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ( r2_hidden(X7,u1_struct_0(X3))
                                   => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7) = k1_funct_1(X6,X7) ) )
                             => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(dt_k3_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_pre_topc(X3,X1)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
     => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
        & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(d9_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_funct_2(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                             => ( ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X4))
                                   => ( r2_hidden(X7,u1_struct_0(X3))
                                     => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7) = k1_funct_1(X6,X7) ) )
                               => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t73_tmap_1])).

fof(c_0_18,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ v1_funct_1(X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k2_partfun1(X28,X29,X30,X31) = k7_relat_1(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_19,negated_conjecture,(
    ! [X61] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk2_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
      & m1_pre_topc(esk4_0,esk5_0)
      & v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      & ( ~ m1_subset_1(X61,u1_struct_0(esk5_0))
        | ~ r2_hidden(X61,u1_struct_0(esk4_0))
        | k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X61) = k1_funct_1(esk7_0,X61) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).

fof(c_0_20,plain,(
    ! [X47,X48,X49,X50,X51] :
      ( ( v1_funct_1(k3_tmap_1(X47,X48,X49,X50,X51))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | ~ m1_pre_topc(X49,X47)
        | ~ m1_pre_topc(X50,X47)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X48))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48)))) )
      & ( v1_funct_2(k3_tmap_1(X47,X48,X49,X50,X51),u1_struct_0(X50),u1_struct_0(X48))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | ~ m1_pre_topc(X49,X47)
        | ~ m1_pre_topc(X50,X47)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X48))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48)))) )
      & ( m1_subset_1(k3_tmap_1(X47,X48,X49,X50,X51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X48))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | ~ m1_pre_topc(X49,X47)
        | ~ m1_pre_topc(X50,X47)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X48))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

fof(c_0_21,plain,(
    ! [X42,X43,X44,X45,X46] :
      ( v2_struct_0(X42)
      | ~ v2_pre_topc(X42)
      | ~ l1_pre_topc(X42)
      | v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | ~ m1_pre_topc(X44,X42)
      | ~ m1_pre_topc(X45,X42)
      | ~ v1_funct_1(X46)
      | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))
      | ~ m1_pre_topc(X45,X44)
      | k3_tmap_1(X42,X43,X44,X45,X46) = k2_partfun1(u1_struct_0(X44),u1_struct_0(X43),X46,u1_struct_0(X45)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

cnf(c_0_22,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( ~ r2_funct_2(X22,X23,X24,X25)
        | ~ m1_subset_1(X26,X22)
        | k1_funct_1(X24,X26) = k1_funct_1(X25,X26)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( m1_subset_1(esk1_4(X22,X23,X24,X25),X22)
        | r2_funct_2(X22,X23,X24,X25)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( k1_funct_1(X24,esk1_4(X22,X23,X24,X25)) != k1_funct_1(X25,esk1_4(X22,X23,X24,X25))
        | r2_funct_2(X22,X23,X24,X25)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

cnf(c_0_26,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_32,plain,(
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_pre_topc(X40,X39)
      | l1_pre_topc(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_33,plain,(
    ! [X36,X37] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | v2_pre_topc(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1) = k7_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0),u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_24]),c_0_23])]),c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_28]),c_0_29]),c_0_24]),c_0_23])]),c_0_30])).

cnf(c_0_47,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0) = k7_relat_1(esk6_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_27]),c_0_28]),c_0_29]),c_0_24]),c_0_23])]),c_0_30]),c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,esk7_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,esk7_0),u1_struct_0(esk4_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_41]),c_0_42]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_56,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_27]),c_0_28]),c_0_29]),c_0_24]),c_0_23])]),c_0_30])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_42]),c_0_43])])).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_42]),c_0_43]),c_0_44])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( k7_relat_1(esk6_0,u1_struct_0(esk4_0)) = k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_41]),c_0_51]),c_0_42]),c_0_43]),c_0_44])]),c_0_45])).

fof(c_0_61,plain,(
    ! [X54] :
      ( ~ l1_pre_topc(X54)
      | m1_pre_topc(X54,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])]),c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_41]),c_0_42]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_64,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0) = k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0)
    | ~ m1_pre_topc(esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_51]),c_0_57]),c_0_58])]),c_0_59]),c_0_60])).

cnf(c_0_65,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_66,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_68,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0) = k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_57])])).

fof(c_0_69,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_72,plain,(
    ! [X52,X53] :
      ( ~ l1_pre_topc(X52)
      | ~ m1_pre_topc(X53,X52)
      | m1_subset_1(u1_struct_0(X53),k1_zfmisc_1(u1_struct_0(X52))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_73,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | ~ v1_xboole_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_74,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_77,plain,(
    ! [X32,X33,X34,X35] :
      ( v1_xboole_0(X32)
      | ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,X32,X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | ~ m1_subset_1(X35,X32)
      | k3_funct_2(X32,X33,X34,X35) = k1_funct_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_79,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ r2_hidden(X16,X17)
      | k1_funct_1(k7_relat_1(X18,X17),X16) = k1_funct_1(X18,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

fof(c_0_80,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | v1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_51]),c_0_57])])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_75])).

cnf(c_0_85,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1) = k1_funct_1(esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1) = k1_funct_1(esk6_0,X1)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_27]),c_0_24]),c_0_23])])).

cnf(c_0_90,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( k1_funct_1(k7_relat_1(X1,u1_struct_0(esk4_0)),esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)) = k1_funct_1(X1,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_75])).

cnf(c_0_92,negated_conjecture,
    ( k7_relat_1(esk6_0,u1_struct_0(esk4_0)) = k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_68])).

cnf(c_0_93,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_23])).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_51]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0))
    | ~ m1_pre_topc(esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_51]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ m1_pre_topc(esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_51]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_97,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)) = k1_funct_1(esk7_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_75]),c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)) = k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_88]),c_0_90])).

fof(c_0_99,plain,(
    ! [X41] :
      ( v2_struct_0(X41)
      | ~ l1_struct_0(X41)
      | ~ v1_xboole_0(u1_struct_0(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_100,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_101,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)) = k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_24]),c_0_93])])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_65]),c_0_57])])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_65]),c_0_57])])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_65]),c_0_57])])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_68])).

cnf(c_0_106,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)) = k1_funct_1(esk7_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_107,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_37]),c_0_102]),c_0_38]),c_0_103]),c_0_39]),c_0_104])]),c_0_105]),c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_110,plain,(
    ! [X38] :
      ( ~ l1_pre_topc(X38)
      | l1_struct_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_111,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])).

cnf(c_0_112,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_113,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_41]),c_0_43])])).

cnf(c_0_114,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:35:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.66/0.86  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.66/0.86  # and selection function SelectCQIPrecWNTNp.
% 0.66/0.86  #
% 0.66/0.86  # Preprocessing time       : 0.029 s
% 0.66/0.86  # Presaturation interreduction done
% 0.66/0.86  
% 0.66/0.86  # Proof found!
% 0.66/0.86  # SZS status Theorem
% 0.66/0.86  # SZS output start CNFRefutation
% 0.66/0.86  fof(t73_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(r2_hidden(X7,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7)=k1_funct_1(X6,X7)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tmap_1)).
% 0.66/0.86  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.66/0.86  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 0.66/0.86  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.66/0.86  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 0.66/0.86  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.66/0.86  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.66/0.86  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.66/0.86  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.66/0.86  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.66/0.86  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.66/0.86  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.66/0.86  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.66/0.86  fof(t72_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 0.66/0.86  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.66/0.86  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.66/0.86  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.66/0.86  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(r2_hidden(X7,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7)=k1_funct_1(X6,X7)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6)))))))))), inference(assume_negation,[status(cth)],[t73_tmap_1])).
% 0.66/0.86  fof(c_0_18, plain, ![X28, X29, X30, X31]:(~v1_funct_1(X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k2_partfun1(X28,X29,X30,X31)=k7_relat_1(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.66/0.86  fof(c_0_19, negated_conjecture, ![X61]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk2_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&(m1_pre_topc(esk4_0,esk5_0)&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X61,u1_struct_0(esk5_0))|(~r2_hidden(X61,u1_struct_0(esk4_0))|k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X61)=k1_funct_1(esk7_0,X61)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).
% 0.66/0.86  fof(c_0_20, plain, ![X47, X48, X49, X50, X51]:(((v1_funct_1(k3_tmap_1(X47,X48,X49,X50,X51))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)|v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|~m1_pre_topc(X49,X47)|~m1_pre_topc(X50,X47)|~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X48))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48))))))&(v1_funct_2(k3_tmap_1(X47,X48,X49,X50,X51),u1_struct_0(X50),u1_struct_0(X48))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)|v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|~m1_pre_topc(X49,X47)|~m1_pre_topc(X50,X47)|~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X48))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48)))))))&(m1_subset_1(k3_tmap_1(X47,X48,X49,X50,X51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X48))))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)|v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|~m1_pre_topc(X49,X47)|~m1_pre_topc(X50,X47)|~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X49),u1_struct_0(X48))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 0.66/0.86  fof(c_0_21, plain, ![X42, X43, X44, X45, X46]:(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|(~m1_pre_topc(X44,X42)|(~m1_pre_topc(X45,X42)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))|(~m1_pre_topc(X45,X44)|k3_tmap_1(X42,X43,X44,X45,X46)=k2_partfun1(u1_struct_0(X44),u1_struct_0(X43),X46,u1_struct_0(X45)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.66/0.86  cnf(c_0_22, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.66/0.86  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  fof(c_0_25, plain, ![X22, X23, X24, X25, X26]:((~r2_funct_2(X22,X23,X24,X25)|(~m1_subset_1(X26,X22)|k1_funct_1(X24,X26)=k1_funct_1(X25,X26))|(~v1_funct_1(X25)|~v1_funct_2(X25,X22,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))|(~v1_funct_1(X24)|~v1_funct_2(X24,X22,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))&((m1_subset_1(esk1_4(X22,X23,X24,X25),X22)|r2_funct_2(X22,X23,X24,X25)|(~v1_funct_1(X25)|~v1_funct_2(X25,X22,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))|(~v1_funct_1(X24)|~v1_funct_2(X24,X22,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))&(k1_funct_1(X24,esk1_4(X22,X23,X24,X25))!=k1_funct_1(X25,esk1_4(X22,X23,X24,X25))|r2_funct_2(X22,X23,X24,X25)|(~v1_funct_1(X25)|~v1_funct_2(X25,X22,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))|(~v1_funct_1(X24)|~v1_funct_2(X24,X22,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 0.66/0.86  cnf(c_0_26, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.66/0.86  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_31, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.66/0.86  fof(c_0_32, plain, ![X39, X40]:(~l1_pre_topc(X39)|(~m1_pre_topc(X40,X39)|l1_pre_topc(X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.66/0.86  fof(c_0_33, plain, ![X36, X37]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|v2_pre_topc(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.66/0.86  cnf(c_0_34, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.66/0.86  cnf(c_0_35, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1)=k7_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.66/0.86  cnf(c_0_36, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.66/0.86  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_40, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0),u1_struct_0(X2),u1_struct_0(esk3_0))|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_24]), c_0_23])]), c_0_30])).
% 0.66/0.86  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_42, negated_conjecture, (m1_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_43, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_44, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_46, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0))|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_27]), c_0_28]), c_0_29]), c_0_24]), c_0_23])]), c_0_30])).
% 0.66/0.86  cnf(c_0_47, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.66/0.86  cnf(c_0_48, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.66/0.86  cnf(c_0_49, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.66/0.86  cnf(c_0_50, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0)=k7_relat_1(esk6_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk5_0)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_27]), c_0_28]), c_0_29]), c_0_24]), c_0_23])]), c_0_30]), c_0_35])).
% 0.66/0.86  cnf(c_0_51, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_52, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,esk7_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,esk7_0),u1_struct_0(esk4_0))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.66/0.86  cnf(c_0_53, negated_conjecture, (v1_funct_2(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44])]), c_0_45])).
% 0.66/0.86  cnf(c_0_54, negated_conjecture, (v1_funct_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_41]), c_0_42]), c_0_43]), c_0_44])]), c_0_45])).
% 0.66/0.86  cnf(c_0_55, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_56, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_27]), c_0_28]), c_0_29]), c_0_24]), c_0_23])]), c_0_30])).
% 0.66/0.86  cnf(c_0_57, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_42]), c_0_43])])).
% 0.66/0.86  cnf(c_0_58, negated_conjecture, (v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_42]), c_0_43]), c_0_44])])).
% 0.66/0.86  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_60, negated_conjecture, (k7_relat_1(esk6_0,u1_struct_0(esk4_0))=k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_41]), c_0_51]), c_0_42]), c_0_43]), c_0_44])]), c_0_45])).
% 0.66/0.86  fof(c_0_61, plain, ![X54]:(~l1_pre_topc(X54)|m1_pre_topc(X54,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.66/0.86  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),u1_struct_0(esk4_0))|~m1_subset_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])]), c_0_55])).
% 0.66/0.86  cnf(c_0_63, negated_conjecture, (m1_subset_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_41]), c_0_42]), c_0_43]), c_0_44])]), c_0_45])).
% 0.66/0.86  cnf(c_0_64, negated_conjecture, (k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0)=k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0)|~m1_pre_topc(esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_51]), c_0_57]), c_0_58])]), c_0_59]), c_0_60])).
% 0.66/0.86  cnf(c_0_65, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.66/0.86  fof(c_0_66, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.66/0.86  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.66/0.86  cnf(c_0_68, negated_conjecture, (k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0)=k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_57])])).
% 0.66/0.86  fof(c_0_69, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.66/0.86  cnf(c_0_70, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.66/0.86  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.66/0.86  fof(c_0_72, plain, ![X52, X53]:(~l1_pre_topc(X52)|(~m1_pre_topc(X53,X52)|m1_subset_1(u1_struct_0(X53),k1_zfmisc_1(u1_struct_0(X52))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.66/0.86  fof(c_0_73, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|~v1_xboole_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.66/0.86  cnf(c_0_74, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.66/0.86  cnf(c_0_75, negated_conjecture, (r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.66/0.86  cnf(c_0_76, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.66/0.86  fof(c_0_77, plain, ![X32, X33, X34, X35]:(v1_xboole_0(X32)|~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~m1_subset_1(X35,X32)|k3_funct_2(X32,X33,X34,X35)=k1_funct_1(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.66/0.86  cnf(c_0_78, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.66/0.86  fof(c_0_79, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|~v1_funct_1(X18)|(~r2_hidden(X16,X17)|k1_funct_1(k7_relat_1(X18,X17),X16)=k1_funct_1(X18,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).
% 0.66/0.86  fof(c_0_80, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.66/0.86  cnf(c_0_81, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),X1)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.66/0.86  cnf(c_0_82, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_51]), c_0_57])])).
% 0.66/0.86  cnf(c_0_83, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.66/0.86  cnf(c_0_84, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(X1)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_78, c_0_75])).
% 0.66/0.86  cnf(c_0_85, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.66/0.86  cnf(c_0_86, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.66/0.86  cnf(c_0_87, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1)=k1_funct_1(esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  cnf(c_0_88, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.66/0.86  cnf(c_0_89, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1)=k1_funct_1(esk6_0,X1)|v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_27]), c_0_24]), c_0_23])])).
% 0.66/0.86  cnf(c_0_90, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_84, c_0_82])).
% 0.66/0.86  cnf(c_0_91, negated_conjecture, (k1_funct_1(k7_relat_1(X1,u1_struct_0(esk4_0)),esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))=k1_funct_1(X1,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_85, c_0_75])).
% 0.66/0.86  cnf(c_0_92, negated_conjecture, (k7_relat_1(esk6_0,u1_struct_0(esk4_0))=k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0)), inference(rw,[status(thm)],[c_0_60, c_0_68])).
% 0.66/0.86  cnf(c_0_93, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_86, c_0_23])).
% 0.66/0.86  cnf(c_0_94, negated_conjecture, (v1_funct_2(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~m1_pre_topc(esk5_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_51]), c_0_57]), c_0_58])]), c_0_59])).
% 0.66/0.86  cnf(c_0_95, negated_conjecture, (v1_funct_1(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0))|~m1_pre_topc(esk5_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_51]), c_0_57]), c_0_58])]), c_0_59])).
% 0.66/0.86  cnf(c_0_96, negated_conjecture, (m1_subset_1(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~m1_pre_topc(esk5_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_51]), c_0_57]), c_0_58])]), c_0_59])).
% 0.66/0.86  cnf(c_0_97, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))=k1_funct_1(esk7_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_75]), c_0_88])).
% 0.66/0.86  cnf(c_0_98, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_88]), c_0_90])).
% 0.66/0.86  fof(c_0_99, plain, ![X41]:(v2_struct_0(X41)|~l1_struct_0(X41)|~v1_xboole_0(u1_struct_0(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.66/0.86  cnf(c_0_100, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk1_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk1_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.66/0.86  cnf(c_0_101, negated_conjecture, (k1_funct_1(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_24]), c_0_93])])).
% 0.66/0.86  cnf(c_0_102, negated_conjecture, (v1_funct_2(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_65]), c_0_57])])).
% 0.66/0.86  cnf(c_0_103, negated_conjecture, (v1_funct_1(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_65]), c_0_57])])).
% 0.66/0.86  cnf(c_0_104, negated_conjecture, (m1_subset_1(k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_65]), c_0_57])])).
% 0.66/0.86  cnf(c_0_105, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[c_0_55, c_0_68])).
% 0.66/0.86  cnf(c_0_106, negated_conjecture, (k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))=k1_funct_1(esk7_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk5_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.66/0.86  cnf(c_0_107, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.66/0.86  cnf(c_0_108, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_37]), c_0_102]), c_0_38]), c_0_103]), c_0_39]), c_0_104])]), c_0_105]), c_0_106])).
% 0.66/0.86  cnf(c_0_109, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.66/0.86  fof(c_0_110, plain, ![X38]:(~l1_pre_topc(X38)|l1_struct_0(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.66/0.86  cnf(c_0_111, negated_conjecture, (~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])).
% 0.66/0.86  cnf(c_0_112, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.66/0.86  cnf(c_0_113, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_41]), c_0_43])])).
% 0.66/0.86  cnf(c_0_114, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113])]), ['proof']).
% 0.66/0.86  # SZS output end CNFRefutation
% 0.66/0.86  # Proof object total steps             : 115
% 0.66/0.86  # Proof object clause steps            : 80
% 0.66/0.86  # Proof object formula steps           : 35
% 0.66/0.86  # Proof object conjectures             : 64
% 0.66/0.86  # Proof object clause conjectures      : 61
% 0.66/0.86  # Proof object formula conjectures     : 3
% 0.66/0.86  # Proof object initial clauses used    : 38
% 0.66/0.86  # Proof object initial formulas used   : 17
% 0.66/0.86  # Proof object generating inferences   : 38
% 0.66/0.86  # Proof object simplifying inferences  : 114
% 0.66/0.86  # Training examples: 0 positive, 0 negative
% 0.66/0.86  # Parsed axioms                        : 17
% 0.66/0.86  # Removed by relevancy pruning/SinE    : 0
% 0.66/0.86  # Initial clauses                      : 39
% 0.66/0.86  # Removed in clause preprocessing      : 0
% 0.66/0.86  # Initial clauses in saturation        : 39
% 0.66/0.86  # Processed clauses                    : 3078
% 0.66/0.86  # ...of these trivial                  : 34
% 0.66/0.86  # ...subsumed                          : 229
% 0.66/0.86  # ...remaining for further processing  : 2815
% 0.66/0.86  # Other redundant clauses eliminated   : 0
% 0.66/0.86  # Clauses deleted for lack of memory   : 0
% 0.66/0.86  # Backward-subsumed                    : 0
% 0.66/0.86  # Backward-rewritten                   : 627
% 0.66/0.86  # Generated clauses                    : 8305
% 0.66/0.86  # ...of the previous two non-trivial   : 8432
% 0.66/0.86  # Contextual simplify-reflections      : 21
% 0.66/0.86  # Paramodulations                      : 8304
% 0.66/0.86  # Factorizations                       : 0
% 0.66/0.86  # Equation resolutions                 : 1
% 0.66/0.86  # Propositional unsat checks           : 0
% 0.66/0.86  #    Propositional check models        : 0
% 0.66/0.86  #    Propositional check unsatisfiable : 0
% 0.66/0.86  #    Propositional clauses             : 0
% 0.66/0.86  #    Propositional clauses after purity: 0
% 0.66/0.86  #    Propositional unsat core size     : 0
% 0.66/0.86  #    Propositional preprocessing time  : 0.000
% 0.66/0.86  #    Propositional encoding time       : 0.000
% 0.66/0.86  #    Propositional solver time         : 0.000
% 0.66/0.86  #    Success case prop preproc time    : 0.000
% 0.66/0.86  #    Success case prop encoding time   : 0.000
% 0.66/0.86  #    Success case prop solver time     : 0.000
% 0.66/0.86  # Current number of processed clauses  : 2149
% 0.66/0.86  #    Positive orientable unit clauses  : 1131
% 0.66/0.86  #    Positive unorientable unit clauses: 0
% 0.66/0.86  #    Negative unit clauses             : 6
% 0.66/0.86  #    Non-unit-clauses                  : 1012
% 0.66/0.86  # Current number of unprocessed clauses: 5274
% 0.66/0.86  # ...number of literals in the above   : 18235
% 0.66/0.86  # Current number of archived formulas  : 0
% 0.66/0.86  # Current number of archived clauses   : 666
% 0.66/0.86  # Clause-clause subsumption calls (NU) : 123617
% 0.66/0.86  # Rec. Clause-clause subsumption calls : 29682
% 0.66/0.86  # Non-unit clause-clause subsumptions  : 250
% 0.66/0.86  # Unit Clause-clause subsumption calls : 134920
% 0.66/0.86  # Rewrite failures with RHS unbound    : 0
% 0.66/0.86  # BW rewrite match attempts            : 65375
% 0.66/0.86  # BW rewrite match successes           : 271
% 0.66/0.86  # Condensation attempts                : 0
% 0.66/0.86  # Condensation successes               : 0
% 0.66/0.86  # Termbank termtop insertions          : 672796
% 0.66/0.86  
% 0.66/0.86  # -------------------------------------------------
% 0.66/0.86  # User time                : 0.494 s
% 0.66/0.86  # System time              : 0.021 s
% 0.66/0.86  # Total time               : 0.515 s
% 0.66/0.86  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
