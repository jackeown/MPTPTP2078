%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:34 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 149 expanded)
%              Number of clauses        :   40 (  51 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 (1501 expanded)
%              Number of equality atoms :   25 ( 100 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_tmap_1,conjecture,(
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
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ( r2_hidden(X6,u1_struct_0(X3))
                             => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X6) = k1_funct_1(k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

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

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(c_0_11,negated_conjecture,(
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
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ( r2_hidden(X6,u1_struct_0(X3))
                               => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X6) = k1_funct_1(k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t72_tmap_1])).

fof(c_0_12,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_pre_topc(X29,X28)
      | l1_pre_topc(X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_13,negated_conjecture,
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
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & r2_hidden(esk7_0,u1_struct_0(esk4_0))
    & k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk7_0) != k1_funct_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X35)
      | m1_subset_1(u1_struct_0(X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_15,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_19,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X24,X25,X26,X27] :
      ( v1_xboole_0(X24)
      | ~ v1_funct_1(X26)
      | ~ v1_funct_2(X26,X24,X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | ~ m1_subset_1(X27,X24)
      | k3_funct_2(X24,X25,X26,X27) = k1_funct_1(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_34,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X30)
      | ~ m1_pre_topc(X33,X30)
      | ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))
      | ~ m1_pre_topc(X33,X32)
      | k3_tmap_1(X30,X31,X32,X33,X34) = k2_partfun1(u1_struct_0(X32),u1_struct_0(X31),X34,u1_struct_0(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

cnf(c_0_35,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1) = k1_funct_1(esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk7_0) != k1_funct_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk7_0) = k1_funct_1(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_30]),c_0_38]),c_0_39]),c_0_31]),c_0_32])]),c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_47,plain,(
    ! [X20,X21,X22,X23] :
      ( ~ v1_funct_1(X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k2_partfun1(X20,X21,X22,X23) = k7_relat_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) != k1_funct_1(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_21]),c_0_16]),c_0_17])]),c_0_46])).

cnf(c_0_50,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_51,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | ~ r2_hidden(X17,X18)
      | k1_funct_1(k7_relat_1(X19,X18),X17) = k1_funct_1(X19,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

fof(c_0_52,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_53,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)),esk7_0) != k1_funct_1(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1) = k7_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_31])])).

cnf(c_0_56,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk6_0,u1_struct_0(esk4_0)),esk7_0) != k1_funct_1(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(k7_relat_1(X1,u1_struct_0(esk4_0)),esk7_0) = k1_funct_1(X1,esk7_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_32]),c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_31]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:51:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.14/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t72_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X6)=k1_funct_1(k3_tmap_1(X1,X2,X4,X3,X5),X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tmap_1)).
% 0.14/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.14/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.14/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.14/0.38  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.14/0.38  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.14/0.38  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.14/0.38  fof(t72_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 0.14/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X6)=k1_funct_1(k3_tmap_1(X1,X2,X4,X3,X5),X6)))))))))), inference(assume_negation,[status(cth)],[t72_tmap_1])).
% 0.14/0.38  fof(c_0_12, plain, ![X28, X29]:(~l1_pre_topc(X28)|(~m1_pre_topc(X29,X28)|l1_pre_topc(X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.14/0.38  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk2_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&(m1_pre_topc(esk4_0,esk5_0)&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(r2_hidden(esk7_0,u1_struct_0(esk4_0))&k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk7_0)!=k1_funct_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.14/0.38  fof(c_0_14, plain, ![X35, X36]:(~l1_pre_topc(X35)|(~m1_pre_topc(X36,X35)|m1_subset_1(u1_struct_0(X36),k1_zfmisc_1(u1_struct_0(X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.14/0.38  cnf(c_0_15, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_18, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.38  fof(c_0_19, plain, ![X11, X12]:(~v1_xboole_0(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.14/0.38  cnf(c_0_20, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.14/0.38  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_25, plain, ![X24, X25, X26, X27]:(v1_xboole_0(X24)|~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|~m1_subset_1(X27,X24)|k3_funct_2(X24,X25,X26,X27)=k1_funct_1(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.14/0.38  cnf(c_0_26, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_29, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.14/0.38  fof(c_0_34, plain, ![X30, X31, X32, X33, X34]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~m1_pre_topc(X32,X30)|(~m1_pre_topc(X33,X30)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))|(~m1_pre_topc(X33,X32)|k3_tmap_1(X30,X31,X32,X33,X34)=k2_partfun1(u1_struct_0(X32),u1_struct_0(X31),X34,u1_struct_0(X33)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1)=k1_funct_1(esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_37, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk7_0)!=k1_funct_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk7_0)=k1_funct_1(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk5_0)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_30]), c_0_38]), c_0_39]), c_0_31]), c_0_32])]), c_0_40])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_47, plain, ![X20, X21, X22, X23]:(~v1_funct_1(X22)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k2_partfun1(X20,X21,X22,X23)=k7_relat_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (k1_funct_1(k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)!=k1_funct_1(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_21]), c_0_16]), c_0_17])]), c_0_46])).
% 0.14/0.38  cnf(c_0_50, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.14/0.38  fof(c_0_51, plain, ![X17, X18, X19]:(~v1_relat_1(X19)|~v1_funct_1(X19)|(~r2_hidden(X17,X18)|k1_funct_1(k7_relat_1(X19,X18),X17)=k1_funct_1(X19,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).
% 0.14/0.38  fof(c_0_52, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.38  fof(c_0_53, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (k1_funct_1(k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)),esk7_0)!=k1_funct_1(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1)=k7_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_32]), c_0_31])])).
% 0.14/0.38  cnf(c_0_56, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.38  cnf(c_0_57, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.38  cnf(c_0_58, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (k1_funct_1(k7_relat_1(esk6_0,u1_struct_0(esk4_0)),esk7_0)!=k1_funct_1(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (k1_funct_1(k7_relat_1(X1,u1_struct_0(esk4_0)),esk7_0)=k1_funct_1(X1,esk7_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_24])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_32]), c_0_58])])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_31]), c_0_61])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 63
% 0.14/0.38  # Proof object clause steps            : 40
% 0.14/0.38  # Proof object formula steps           : 23
% 0.14/0.38  # Proof object conjectures             : 33
% 0.14/0.38  # Proof object clause conjectures      : 30
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 25
% 0.14/0.38  # Proof object initial formulas used   : 11
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 31
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 11
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 28
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 28
% 0.14/0.38  # Processed clauses                    : 88
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 3
% 0.14/0.38  # ...remaining for further processing  : 84
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 7
% 0.14/0.38  # Generated clauses                    : 29
% 0.14/0.38  # ...of the previous two non-trivial   : 33
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 29
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 49
% 0.14/0.38  #    Positive orientable unit clauses  : 22
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 8
% 0.14/0.38  #    Non-unit-clauses                  : 19
% 0.14/0.38  # Current number of unprocessed clauses: 1
% 0.14/0.38  # ...number of literals in the above   : 4
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 35
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 263
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 20
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.38  # Unit Clause-clause subsumption calls : 16
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 9
% 0.14/0.38  # BW rewrite match successes           : 5
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3013
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.030 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.036 s
% 0.14/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
