%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  123 (11247 expanded)
%              Number of clauses        :   92 (3889 expanded)
%              Number of leaves         :   15 (2604 expanded)
%              Depth                    :   16
%              Number of atoms          :  426 (167053 expanded)
%              Number of equality atoms :   51 (8567 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_tmap_1,conjecture,(
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
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                         => ! [X7] :
                              ( ( v1_funct_1(X7)
                                & v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
                                & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                             => ( ( X4 = X1
                                  & r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7) )
                               => ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)
                                <=> r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_15,negated_conjecture,(
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
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                               => ( ( X4 = X1
                                    & r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7) )
                                 => ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)
                                  <=> r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t80_tmap_1])).

fof(c_0_16,negated_conjecture,
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
    & v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
    & esk5_0 = esk2_0
    & r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk8_0)
    & ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)
      | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) )
    & ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)
      | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_17,plain,(
    ! [X45,X46,X47,X48,X49] :
      ( v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | v2_struct_0(X46)
      | ~ v2_pre_topc(X46)
      | ~ l1_pre_topc(X46)
      | ~ m1_pre_topc(X47,X45)
      | ~ m1_pre_topc(X48,X45)
      | ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X46))
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X46))))
      | ~ m1_pre_topc(X48,X47)
      | k3_tmap_1(X45,X46,X47,X48,X49) = k2_partfun1(u1_struct_0(X47),u1_struct_0(X46),X49,u1_struct_0(X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_18,plain,(
    ! [X50,X51,X52] :
      ( ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | ~ m1_pre_topc(X51,X50)
      | ~ m1_pre_topc(X52,X51)
      | m1_pre_topc(X52,X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_19,plain,(
    ! [X41,X42,X43,X44] :
      ( v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | v2_struct_0(X42)
      | ~ v2_pre_topc(X42)
      | ~ l1_pre_topc(X42)
      | ~ v1_funct_1(X43)
      | ~ v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))
      | ~ m1_pre_topc(X44,X41)
      | k2_tmap_1(X41,X42,X43,X44) = k2_partfun1(u1_struct_0(X41),u1_struct_0(X42),X43,u1_struct_0(X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk5_0 = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_35,plain,(
    ! [X29,X30,X31] :
      ( ( v4_relat_1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v5_relat_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_36,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_37,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_38,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk3_0,esk8_0,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])]),c_0_33]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_41,plain,(
    ! [X24,X25] :
      ( ( ~ v5_relat_1(X25,X24)
        | r1_tarski(k2_relat_1(X25),X24)
        | ~ v1_relat_1(X25) )
      & ( ~ r1_tarski(k2_relat_1(X25),X24)
        | v5_relat_1(X25,X24)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_42,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_45,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_46,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk2_0,X2,esk8_0) = k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_27]),c_0_29]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_53,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ r1_tarski(k1_relat_1(X34),X32)
      | ~ r1_tarski(k2_relat_1(X34),X33)
      | m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_54,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( v5_relat_1(esk8_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_32])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_47])).

fof(c_0_61,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( ~ r1_funct_2(X35,X36,X37,X38,X39,X40)
        | X39 = X40
        | v1_xboole_0(X36)
        | v1_xboole_0(X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X35,X36)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X37,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X39 != X40
        | r1_funct_2(X35,X36,X37,X38,X39,X40)
        | v1_xboole_0(X36)
        | v1_xboole_0(X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X35,X36)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X37,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_62,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_64,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk2_0,esk4_0,esk8_0) = k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_40]),c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_21])).

cnf(c_0_66,negated_conjecture,
    ( v5_relat_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( v5_relat_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_52])).

cnf(c_0_69,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_52])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk8_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_75,plain,
    ( X5 = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ r1_funct_2(X1,X2,X3,X4,X5,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_21])).

cnf(c_0_80,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0) = k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_28]),c_0_30])]),c_0_34])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_66]),c_0_67])])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_68]),c_0_69])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ r1_tarski(k1_relat_1(esk8_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_56])])).

cnf(c_0_84,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

fof(c_0_86,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_87,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( esk8_0 = esk6_0
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_26]),c_0_77]),c_0_31]),c_0_78]),c_0_32]),c_0_52])])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0),esk7_0)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ r1_tarski(k1_relat_1(esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_81]),c_0_67])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_82]),c_0_69])])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk8_0),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_60])).

cnf(c_0_94,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_95,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_96,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk6_0),esk7_0)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk6_0) = k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_88])).

fof(c_0_99,plain,(
    ! [X17,X18] :
      ( ( k2_zfmisc_1(X17,X18) != k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_60])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk6_0),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_60])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(k1_relat_1(esk8_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_105,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(k1_relat_1(esk7_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(k1_relat_1(esk6_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_101])).

cnf(c_0_108,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_85])).

cnf(c_0_109,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk8_0),u1_struct_0(esk3_0)) = esk8_0
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk8_0),u1_struct_0(esk3_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_111,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_105])).

cnf(c_0_112,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk7_0),u1_struct_0(esk3_0)) = esk7_0
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk7_0),u1_struct_0(esk3_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk6_0),u1_struct_0(esk3_0)) = esk6_0
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk6_0),u1_struct_0(esk3_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_107])).

cnf(c_0_114,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),X1,k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)
    | r2_funct_2(u1_struct_0(esk4_0),X1,k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_108])).

cnf(c_0_115,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110]),c_0_111]),c_0_110]),c_0_111]),c_0_95])])).

cnf(c_0_116,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_110]),c_0_111]),c_0_110]),c_0_111]),c_0_95])])).

cnf(c_0_117,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_110]),c_0_111]),c_0_110]),c_0_111]),c_0_95])])).

cnf(c_0_118,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_104,c_0_110])).

cnf(c_0_119,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),X1,k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)
    | ~ r2_funct_2(u1_struct_0(esk4_0),X1,k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_108])).

cnf(c_0_120,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),X1,k2_tmap_1(esk2_0,esk3_0,k1_xboole_0,esk4_0),k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_80]),c_0_115]),c_0_116]),c_0_117]),c_0_116]),c_0_110]),c_0_118])])).

cnf(c_0_121,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_80]),c_0_115]),c_0_116]),c_0_117]),c_0_116]),c_0_110]),c_0_118])]),c_0_120])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_118,c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.48  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.029 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t80_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 0.19/0.48  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.19/0.48  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.19/0.48  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.19/0.48  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.48  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.48  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.48  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.48  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.48  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.48  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.19/0.48  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.48  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.48  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6))))))))))), inference(assume_negation,[status(cth)],[t80_tmap_1])).
% 0.19/0.48  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk2_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&((esk5_0=esk2_0&r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk8_0))&((~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0))&(r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.48  fof(c_0_17, plain, ![X45, X46, X47, X48, X49]:(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)|(~m1_pre_topc(X47,X45)|(~m1_pre_topc(X48,X45)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X46))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X46))))|(~m1_pre_topc(X48,X47)|k3_tmap_1(X45,X46,X47,X48,X49)=k2_partfun1(u1_struct_0(X47),u1_struct_0(X46),X49,u1_struct_0(X48)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.19/0.48  fof(c_0_18, plain, ![X50, X51, X52]:(~v2_pre_topc(X50)|~l1_pre_topc(X50)|(~m1_pre_topc(X51,X50)|(~m1_pre_topc(X52,X51)|m1_pre_topc(X52,X50)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.19/0.48  fof(c_0_19, plain, ![X41, X42, X43, X44]:(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))|(~m1_pre_topc(X44,X41)|k2_tmap_1(X41,X42,X43,X44)=k2_partfun1(u1_struct_0(X41),u1_struct_0(X42),X43,u1_struct_0(X44)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.19/0.48  cnf(c_0_20, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_21, negated_conjecture, (esk5_0=esk2_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_23, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.48  cnf(c_0_24, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.48  cnf(c_0_25, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.48  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.19/0.48  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  fof(c_0_35, plain, ![X29, X30, X31]:((v4_relat_1(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v5_relat_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.48  fof(c_0_36, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.48  fof(c_0_37, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.48  cnf(c_0_38, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.48  cnf(c_0_39, negated_conjecture, (k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(X1))=k2_tmap_1(esk2_0,esk3_0,esk8_0,X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])]), c_0_33]), c_0_34])).
% 0.19/0.48  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  fof(c_0_41, plain, ![X24, X25]:((~v5_relat_1(X25,X24)|r1_tarski(k2_relat_1(X25),X24)|~v1_relat_1(X25))&(~r1_tarski(k2_relat_1(X25),X24)|v5_relat_1(X25,X24)|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.48  cnf(c_0_42, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.48  cnf(c_0_43, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.48  fof(c_0_44, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|~v1_xboole_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.48  fof(c_0_45, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.48  fof(c_0_46, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.48  cnf(c_0_47, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.48  cnf(c_0_48, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk2_0,X2,esk8_0)=k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk2_0)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_26]), c_0_27]), c_0_29]), c_0_31]), c_0_32])]), c_0_33])).
% 0.19/0.48  cnf(c_0_49, negated_conjecture, (k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk8_0,u1_struct_0(esk4_0))=k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.48  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  fof(c_0_53, plain, ![X32, X33, X34]:(~v1_relat_1(X34)|(~r1_tarski(k1_relat_1(X34),X32)|~r1_tarski(k2_relat_1(X34),X33)|m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.48  cnf(c_0_54, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.48  cnf(c_0_55, negated_conjecture, (v5_relat_1(esk8_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_32])).
% 0.19/0.48  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_43, c_0_32])).
% 0.19/0.48  cnf(c_0_57, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.48  cnf(c_0_58, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.48  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.48  cnf(c_0_60, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_47])).
% 0.19/0.48  fof(c_0_61, plain, ![X35, X36, X37, X38, X39, X40]:((~r1_funct_2(X35,X36,X37,X38,X39,X40)|X39=X40|(v1_xboole_0(X36)|v1_xboole_0(X38)|~v1_funct_1(X39)|~v1_funct_2(X39,X35,X36)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~v1_funct_1(X40)|~v1_funct_2(X40,X37,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&(X39!=X40|r1_funct_2(X35,X36,X37,X38,X39,X40)|(v1_xboole_0(X36)|v1_xboole_0(X38)|~v1_funct_1(X39)|~v1_funct_2(X39,X35,X36)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~v1_funct_1(X40)|~v1_funct_2(X40,X37,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.19/0.48  cnf(c_0_62, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_63, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_64, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk2_0,esk4_0,esk8_0)=k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_40]), c_0_49])).
% 0.19/0.48  cnf(c_0_65, negated_conjecture, (m1_pre_topc(esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_50, c_0_21])).
% 0.19/0.48  cnf(c_0_66, negated_conjecture, (v5_relat_1(esk7_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_51])).
% 0.19/0.48  cnf(c_0_67, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_43, c_0_51])).
% 0.19/0.48  cnf(c_0_68, negated_conjecture, (v5_relat_1(esk6_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_52])).
% 0.19/0.48  cnf(c_0_69, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_43, c_0_52])).
% 0.19/0.48  cnf(c_0_70, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.48  cnf(c_0_71, negated_conjecture, (r1_tarski(k2_relat_1(esk8_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.19/0.48  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.48  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.48  cnf(c_0_74, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk8_0),esk7_0)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_75, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.48  cnf(c_0_76, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_62, c_0_21])).
% 0.19/0.48  cnf(c_0_77, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_78, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_79, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(rw,[status(thm)],[c_0_63, c_0_21])).
% 0.19/0.48  cnf(c_0_80, negated_conjecture, (k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0)=k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_28]), c_0_30])]), c_0_34])).
% 0.19/0.48  cnf(c_0_81, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_66]), c_0_67])])).
% 0.19/0.48  cnf(c_0_82, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_68]), c_0_69])])).
% 0.19/0.48  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~r1_tarski(k1_relat_1(esk8_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_56])])).
% 0.19/0.48  cnf(c_0_84, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.48  cnf(c_0_85, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.48  fof(c_0_86, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.48  cnf(c_0_87, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(rw,[status(thm)],[c_0_74, c_0_21])).
% 0.19/0.48  cnf(c_0_88, negated_conjecture, (esk8_0=esk6_0|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_26]), c_0_77]), c_0_31]), c_0_78]), c_0_32]), c_0_52])])).
% 0.19/0.48  cnf(c_0_89, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk8_0,esk4_0),esk7_0)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.48  cnf(c_0_90, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~r1_tarski(k1_relat_1(esk7_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_81]), c_0_67])])).
% 0.19/0.48  cnf(c_0_91, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~r1_tarski(k1_relat_1(esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_82]), c_0_69])])).
% 0.19/0.48  cnf(c_0_92, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.48  cnf(c_0_93, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk8_0),u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_83, c_0_60])).
% 0.19/0.48  cnf(c_0_94, plain, (X1=X2|~v1_xboole_0(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.48  cnf(c_0_95, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.48  cnf(c_0_96, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk6_0),esk7_0)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.19/0.48  cnf(c_0_97, negated_conjecture, (k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk6_0)=k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_80, c_0_88])).
% 0.19/0.48  cnf(c_0_98, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)), inference(spm,[status(thm)],[c_0_89, c_0_88])).
% 0.19/0.48  fof(c_0_99, plain, ![X17, X18]:((k2_zfmisc_1(X17,X18)!=k1_xboole_0|(X17=k1_xboole_0|X18=k1_xboole_0))&((X17!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0)&(X18!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.48  cnf(c_0_100, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_90, c_0_60])).
% 0.19/0.48  cnf(c_0_101, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk6_0),u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_91, c_0_60])).
% 0.19/0.48  cnf(c_0_102, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(k1_relat_1(esk8_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.48  cnf(c_0_103, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.48  cnf(c_0_104, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])).
% 0.19/0.48  cnf(c_0_105, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.19/0.48  cnf(c_0_106, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(k1_relat_1(esk7_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_92, c_0_100])).
% 0.19/0.48  cnf(c_0_107, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(k1_relat_1(esk6_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_92, c_0_101])).
% 0.19/0.48  cnf(c_0_108, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_94, c_0_85])).
% 0.19/0.48  cnf(c_0_109, negated_conjecture, (k2_zfmisc_1(k1_relat_1(esk8_0),u1_struct_0(esk3_0))=esk8_0|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk8_0),u1_struct_0(esk3_0)),esk8_0)), inference(spm,[status(thm)],[c_0_84, c_0_102])).
% 0.19/0.48  cnf(c_0_110, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.19/0.48  cnf(c_0_111, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_105])).
% 0.19/0.48  cnf(c_0_112, negated_conjecture, (k2_zfmisc_1(k1_relat_1(esk7_0),u1_struct_0(esk3_0))=esk7_0|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk7_0),u1_struct_0(esk3_0)),esk7_0)), inference(spm,[status(thm)],[c_0_84, c_0_106])).
% 0.19/0.48  cnf(c_0_113, negated_conjecture, (k2_zfmisc_1(k1_relat_1(esk6_0),u1_struct_0(esk3_0))=esk6_0|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk6_0),u1_struct_0(esk3_0)),esk6_0)), inference(spm,[status(thm)],[c_0_84, c_0_107])).
% 0.19/0.48  cnf(c_0_114, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),X1,k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)|r2_funct_2(u1_struct_0(esk4_0),X1,k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)|~v1_xboole_0(u1_struct_0(esk3_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_87, c_0_108])).
% 0.19/0.48  cnf(c_0_115, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110]), c_0_111]), c_0_110]), c_0_111]), c_0_95])])).
% 0.19/0.48  cnf(c_0_116, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_110]), c_0_111]), c_0_110]), c_0_111]), c_0_95])])).
% 0.19/0.48  cnf(c_0_117, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_110]), c_0_111]), c_0_110]), c_0_111]), c_0_95])])).
% 0.19/0.48  cnf(c_0_118, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_104, c_0_110])).
% 0.19/0.48  cnf(c_0_119, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),X1,k3_tmap_1(esk2_0,esk3_0,esk2_0,esk4_0,esk8_0),esk7_0)|~r2_funct_2(u1_struct_0(esk4_0),X1,k2_tmap_1(esk2_0,esk3_0,esk6_0,esk4_0),esk7_0)|~v1_xboole_0(u1_struct_0(esk3_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_79, c_0_108])).
% 0.19/0.48  cnf(c_0_120, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),X1,k2_tmap_1(esk2_0,esk3_0,k1_xboole_0,esk4_0),k1_xboole_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_80]), c_0_115]), c_0_116]), c_0_117]), c_0_116]), c_0_110]), c_0_118])])).
% 0.19/0.48  cnf(c_0_121, negated_conjecture, (~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_80]), c_0_115]), c_0_116]), c_0_117]), c_0_116]), c_0_110]), c_0_118])]), c_0_120])).
% 0.19/0.48  cnf(c_0_122, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_118, c_0_121]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 123
% 0.19/0.48  # Proof object clause steps            : 92
% 0.19/0.48  # Proof object formula steps           : 31
% 0.19/0.48  # Proof object conjectures             : 70
% 0.19/0.48  # Proof object clause conjectures      : 67
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 35
% 0.19/0.48  # Proof object initial formulas used   : 15
% 0.19/0.48  # Proof object generating inferences   : 40
% 0.19/0.48  # Proof object simplifying inferences  : 87
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 15
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 47
% 0.19/0.48  # Removed in clause preprocessing      : 0
% 0.19/0.48  # Initial clauses in saturation        : 47
% 0.19/0.48  # Processed clauses                    : 1403
% 0.19/0.48  # ...of these trivial                  : 28
% 0.19/0.48  # ...subsumed                          : 798
% 0.19/0.48  # ...remaining for further processing  : 577
% 0.19/0.48  # Other redundant clauses eliminated   : 7
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 31
% 0.19/0.48  # Backward-rewritten                   : 355
% 0.19/0.48  # Generated clauses                    : 3907
% 0.19/0.48  # ...of the previous two non-trivial   : 4020
% 0.19/0.48  # Contextual simplify-reflections      : 7
% 0.19/0.48  # Paramodulations                      : 3899
% 0.19/0.48  # Factorizations                       : 0
% 0.19/0.48  # Equation resolutions                 : 7
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 140
% 0.19/0.48  #    Positive orientable unit clauses  : 28
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 4
% 0.19/0.48  #    Non-unit-clauses                  : 108
% 0.19/0.48  # Current number of unprocessed clauses: 2675
% 0.19/0.48  # ...number of literals in the above   : 12228
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 432
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 42706
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 23784
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 833
% 0.19/0.48  # Unit Clause-clause subsumption calls : 738
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 59
% 0.19/0.48  # BW rewrite match successes           : 10
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 61449
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.142 s
% 0.19/0.49  # System time              : 0.008 s
% 0.19/0.49  # Total time               : 0.150 s
% 0.19/0.49  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
