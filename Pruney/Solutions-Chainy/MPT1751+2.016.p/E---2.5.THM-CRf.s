%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:24 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 175 expanded)
%              Number of clauses        :   45 (  67 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  225 (1109 expanded)
%              Number of equality atoms :   26 (  86 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_tmap_1,conjecture,(
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
                & m1_pre_topc(X3,X2) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( r1_tarski(X5,u1_struct_0(X3))
                       => k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).

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

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(c_0_14,negated_conjecture,(
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
                  & m1_pre_topc(X3,X2) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                       => ( r1_tarski(X5,u1_struct_0(X3))
                         => k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_tmap_1])).

fof(c_0_15,plain,(
    ! [X38,X39,X40,X41] :
      ( v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ v1_funct_1(X40)
      | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))
      | ~ m1_pre_topc(X41,X38)
      | k2_tmap_1(X38,X39,X40,X41) = k2_partfun1(u1_struct_0(X38),u1_struct_0(X39),X40,u1_struct_0(X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r1_tarski(esk5_0,u1_struct_0(esk3_0))
    & k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X34,X35,X36,X37] :
      ( ~ v1_funct_1(X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k2_partfun1(X34,X35,X36,X37) = k7_relat_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_18,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

fof(c_0_30,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k7_relset_1(X27,X28,X29,X30) = k9_relat_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_31,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( k2_tmap_1(esk2_0,esk1_0,esk4_0,X1) = k7_relat_1(esk4_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25]),c_0_19])])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(k1_relat_1(X33),X31)
      | ~ r1_tarski(k2_relat_1(X33),X32)
      | m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_36,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_37,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1) = k9_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_19])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_40,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_41,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_42,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k9_relat_1(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k2_relat_1(X3),X2)
    | ~ r1_tarski(k1_relat_1(X3),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_38])).

fof(c_0_44,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | r1_tarski(k1_relat_1(k7_relat_1(X21,X20)),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_45,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X24,X25,X26] :
      ( ( v4_relat_1(X26,X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v5_relat_1(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_48,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k9_relat_1(esk4_0,esk5_0)
    | ~ v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))),u1_struct_0(esk1_0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_19]),c_0_46])])).

fof(c_0_53,plain,(
    ! [X13,X14] :
      ( ( ~ v5_relat_1(X14,X13)
        | r1_tarski(k2_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k2_relat_1(X14),X13)
        | v5_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_54,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k9_relat_1(esk4_0,esk5_0)
    | ~ v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k9_relat_1(esk4_0,esk5_0)
    | ~ v5_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),u1_struct_0(esk1_0))
    | ~ v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( v5_relat_1(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_46])])).

fof(c_0_66,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X17)
      | ~ r1_tarski(X18,X19)
      | k9_relat_1(k7_relat_1(X17,X19),X18) = k9_relat_1(X17,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k9_relat_1(esk4_0,esk5_0)
    | ~ r1_tarski(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_68,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_70,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | r1_tarski(k7_relat_1(X23,X22),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_52]),c_0_69])])).

cnf(c_0_72,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.21/0.40  # and selection function PSelectComplexExceptRRHorn.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.042 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t61_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(X5,u1_struct_0(X3))=>k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5)=k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 0.21/0.40  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.21/0.40  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.21/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.21/0.40  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.21/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.40  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.21/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.21/0.40  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.21/0.40  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.21/0.40  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 0.21/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(X5,u1_struct_0(X3))=>k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5)=k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t61_tmap_1])).
% 0.21/0.40  fof(c_0_15, plain, ![X38, X39, X40, X41]:(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))|(~m1_pre_topc(X41,X38)|k2_tmap_1(X38,X39,X40,X41)=k2_partfun1(u1_struct_0(X38),u1_struct_0(X39),X40,u1_struct_0(X41)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.21/0.40  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r1_tarski(esk5_0,u1_struct_0(esk3_0))&k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.21/0.40  fof(c_0_17, plain, ![X34, X35, X36, X37]:(~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k2_partfun1(X34,X35,X36,X37)=k7_relat_1(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.21/0.40  cnf(c_0_18, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_20, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_28, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  cnf(c_0_29, negated_conjecture, (k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1))=k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26]), c_0_27])).
% 0.21/0.41  fof(c_0_30, plain, ![X27, X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k7_relset_1(X27,X28,X29,X30)=k9_relat_1(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.21/0.41  cnf(c_0_31, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_32, negated_conjecture, (k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)=k7_relat_1(esk4_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_25]), c_0_19])])).
% 0.21/0.41  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_34, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  fof(c_0_35, plain, ![X31, X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(k1_relat_1(X33),X31)|~r1_tarski(k2_relat_1(X33),X32)|m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.21/0.41  cnf(c_0_36, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.21/0.41  cnf(c_0_37, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1)=k9_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_19])).
% 0.21/0.41  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.41  fof(c_0_39, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.41  fof(c_0_40, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.41  fof(c_0_41, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.41  cnf(c_0_42, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k9_relat_1(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.41  cnf(c_0_43, plain, (k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)|~v1_relat_1(X3)|~r1_tarski(k2_relat_1(X3),X2)|~r1_tarski(k1_relat_1(X3),X1)), inference(spm,[status(thm)],[c_0_34, c_0_38])).
% 0.21/0.41  fof(c_0_44, plain, ![X20, X21]:(~v1_relat_1(X21)|r1_tarski(k1_relat_1(k7_relat_1(X21,X20)),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.21/0.41  cnf(c_0_45, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.41  cnf(c_0_46, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.41  fof(c_0_47, plain, ![X24, X25, X26]:((v4_relat_1(X26,X24)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(v5_relat_1(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.41  fof(c_0_48, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.21/0.41  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.41  cnf(c_0_50, negated_conjecture, (k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k9_relat_1(esk4_0,esk5_0)|~v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)))|~r1_tarski(k2_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))),u1_struct_0(esk1_0))|~r1_tarski(k1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.41  cnf(c_0_51, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_19]), c_0_46])])).
% 0.21/0.41  fof(c_0_53, plain, ![X13, X14]:((~v5_relat_1(X14,X13)|r1_tarski(k2_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k2_relat_1(X14),X13)|v5_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.21/0.41  cnf(c_0_54, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.41  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.41  cnf(c_0_56, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_49, c_0_19])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k9_relat_1(esk4_0,esk5_0)|~v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)))|~r1_tarski(k2_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.21/0.41  cnf(c_0_59, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.41  cnf(c_0_60, plain, (v5_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.41  cnf(c_0_61, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.41  cnf(c_0_62, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_55])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k9_relat_1(esk4_0,esk5_0)|~v5_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),u1_struct_0(esk1_0))|~v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.41  cnf(c_0_64, negated_conjecture, (v5_relat_1(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.41  cnf(c_0_65, negated_conjecture, (v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_46])])).
% 0.21/0.41  fof(c_0_66, plain, ![X17, X18, X19]:(~v1_relat_1(X17)|(~r1_tarski(X18,X19)|k9_relat_1(k7_relat_1(X17,X19),X18)=k9_relat_1(X17,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.21/0.41  cnf(c_0_67, negated_conjecture, (k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k9_relat_1(esk4_0,esk5_0)|~r1_tarski(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.21/0.41  cnf(c_0_68, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.41  cnf(c_0_69, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  fof(c_0_70, plain, ![X22, X23]:(~v1_relat_1(X23)|r1_tarski(k7_relat_1(X23,X22),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.21/0.41  cnf(c_0_71, negated_conjecture, (~r1_tarski(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_52]), c_0_69])])).
% 0.21/0.41  cnf(c_0_72, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.21/0.41  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_52])]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 74
% 0.21/0.41  # Proof object clause steps            : 45
% 0.21/0.41  # Proof object formula steps           : 29
% 0.21/0.41  # Proof object conjectures             : 31
% 0.21/0.41  # Proof object clause conjectures      : 28
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 26
% 0.21/0.41  # Proof object initial formulas used   : 14
% 0.21/0.41  # Proof object generating inferences   : 18
% 0.21/0.41  # Proof object simplifying inferences  : 27
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 14
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 30
% 0.21/0.41  # Removed in clause preprocessing      : 0
% 0.21/0.41  # Initial clauses in saturation        : 30
% 0.21/0.41  # Processed clauses                    : 166
% 0.21/0.41  # ...of these trivial                  : 0
% 0.21/0.41  # ...subsumed                          : 25
% 0.21/0.41  # ...remaining for further processing  : 141
% 0.21/0.41  # Other redundant clauses eliminated   : 0
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 1
% 0.21/0.41  # Backward-rewritten                   : 3
% 0.21/0.41  # Generated clauses                    : 179
% 0.21/0.41  # ...of the previous two non-trivial   : 174
% 0.21/0.41  # Contextual simplify-reflections      : 2
% 0.21/0.41  # Paramodulations                      : 179
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 0
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 107
% 0.21/0.41  #    Positive orientable unit clauses  : 20
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 6
% 0.21/0.41  #    Non-unit-clauses                  : 81
% 0.21/0.41  # Current number of unprocessed clauses: 68
% 0.21/0.41  # ...number of literals in the above   : 281
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 34
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 1973
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 1308
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 27
% 0.21/0.41  # Unit Clause-clause subsumption calls : 99
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 2
% 0.21/0.41  # BW rewrite match successes           : 2
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 5692
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.057 s
% 0.21/0.41  # System time              : 0.006 s
% 0.21/0.41  # Total time               : 0.063 s
% 0.21/0.41  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
