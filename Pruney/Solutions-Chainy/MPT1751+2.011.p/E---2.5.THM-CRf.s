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
% DateTime   : Thu Dec  3 11:17:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 190 expanded)
%              Number of clauses        :   44 (  67 expanded)
%              Number of leaves         :   12 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  257 (1563 expanded)
%              Number of equality atoms :   24 ( 126 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   21 (   2 average)
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

fof(t44_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k7_relset_1(X1,X2,X4,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t178_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ~ v1_xboole_0(X4)
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X1,X4)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) )
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k7_relset_1(X1,X4,X5,X2),X3) )
           => ( v1_funct_1(k2_partfun1(X1,X4,X5,X2))
              & v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3)
              & m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X31,X32,X33,X34] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ v1_funct_1(X33)
      | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X32))
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
      | ~ m1_pre_topc(X34,X31)
      | k2_tmap_1(X31,X32,X33,X34) = k2_partfun1(u1_struct_0(X31),u1_struct_0(X32),X33,u1_struct_0(X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_14,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_15,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,X25,X26)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | r1_tarski(k7_relset_1(X25,X26,X28,X27),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_2])])).

fof(c_0_26,plain,(
    ! [X12,X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | k7_relset_1(X12,X13,X14,X15) = k9_relat_1(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_27,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( k2_tmap_1(esk2_0,esk1_0,esk4_0,X1) = k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ v1_funct_1(X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k2_partfun1(X16,X17,X18,X19) = k7_relat_1(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_31,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X6)
      | ~ r1_tarski(X7,X8)
      | k9_relat_1(k7_relat_1(X6,X8),X7) = k9_relat_1(X6,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_32,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(k7_relset_1(X2,X3,X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | m1_pre_topc(X35,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_36,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(esk3_0)),esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_37,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( v1_funct_1(k2_partfun1(X20,X23,X24,X21))
        | ~ r1_tarski(X21,X20)
        | ~ r1_tarski(k7_relset_1(X20,X23,X24,X21),X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X20,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X23)))
        | v1_xboole_0(X23) )
      & ( v1_funct_2(k2_partfun1(X20,X23,X24,X21),X21,X22)
        | ~ r1_tarski(X21,X20)
        | ~ r1_tarski(k7_relset_1(X20,X23,X24,X21),X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X20,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X23)))
        | v1_xboole_0(X23) )
      & ( m1_subset_1(k2_partfun1(X20,X23,X24,X21),k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ r1_tarski(X21,X20)
        | ~ r1_tarski(k7_relset_1(X20,X23,X24,X21),X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X20,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X23)))
        | v1_xboole_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t178_funct_2])])])])])).

cnf(c_0_41,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_funct_2(X1,X4,X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_42,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r1_tarski(u1_struct_0(X37),u1_struct_0(X38))
        | m1_pre_topc(X37,X38)
        | ~ m1_pre_topc(X38,X36)
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ m1_pre_topc(X37,X38)
        | r1_tarski(u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_pre_topc(X38,X36)
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_43,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_22]),c_0_16])])).

cnf(c_0_45,plain,
    ( k7_relset_1(X1,X2,k7_relat_1(X3,X4),X5) = k9_relat_1(X3,X5)
    | ~ m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X5,X4)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_48,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | v1_xboole_0(X2)
    | ~ r1_tarski(X4,X1)
    | ~ r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk4_0,X1),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_16]),c_0_21]),c_0_22])])).

cnf(c_0_50,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( k9_relat_1(esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),X2)
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_16]),c_0_21]),c_0_22])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k7_relset_1(X1,X2,esk4_0,X3),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_18]),c_0_20])])).

cnf(c_0_56,negated_conjecture,
    ( k9_relat_1(esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k2_partfun1(X1,X2,esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_37]),c_0_22])])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_16])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_29])).

fof(c_0_59,plain,(
    ! [X30] :
      ( v2_struct_0(X30)
      | ~ l1_struct_0(X30)
      | ~ v1_xboole_0(u1_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_60,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_61,negated_conjecture,
    ( k7_relset_1(X1,X2,esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k2_partfun1(X3,X4,esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | k7_relset_1(X1,X2,esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_16])])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_16])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_19])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.19/0.38  # and selection function PSelectComplexExceptRRHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t61_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(X5,u1_struct_0(X3))=>k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5)=k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 0.19/0.38  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.19/0.38  fof(t44_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k7_relset_1(X1,X2,X4,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_2)).
% 0.19/0.38  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.38  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.38  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.19/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.38  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.19/0.38  fof(t178_funct_2, axiom, ![X1, X2, X3, X4]:(~(v1_xboole_0(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=>((r1_tarski(X2,X1)&r1_tarski(k7_relset_1(X1,X4,X5,X2),X3))=>((v1_funct_1(k2_partfun1(X1,X4,X5,X2))&v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3))&m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 0.19/0.38  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.19/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(X5,u1_struct_0(X3))=>k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5)=k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t61_tmap_1])).
% 0.19/0.38  fof(c_0_13, plain, ![X31, X32, X33, X34]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))|(~m1_pre_topc(X34,X31)|k2_tmap_1(X31,X32,X33,X34)=k2_partfun1(u1_struct_0(X31),u1_struct_0(X32),X33,u1_struct_0(X34)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.19/0.38  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r1_tarski(esk5_0,u1_struct_0(esk3_0))&k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.19/0.38  cnf(c_0_15, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  fof(c_0_25, plain, ![X25, X26, X27, X28]:(~v1_funct_1(X28)|~v1_funct_2(X28,X25,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|r1_tarski(k7_relset_1(X25,X26,X28,X27),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_2])])).
% 0.19/0.38  fof(c_0_26, plain, ![X12, X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|k7_relset_1(X12,X13,X14,X15)=k9_relat_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)=k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  fof(c_0_30, plain, ![X16, X17, X18, X19]:(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k2_partfun1(X16,X17,X18,X19)=k7_relat_1(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.38  fof(c_0_31, plain, ![X6, X7, X8]:(~v1_relat_1(X6)|(~r1_tarski(X7,X8)|k9_relat_1(k7_relat_1(X6,X8),X7)=k9_relat_1(X6,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.19/0.38  fof(c_0_32, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|v1_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.38  cnf(c_0_33, plain, (r1_tarski(k7_relset_1(X2,X3,X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_34, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  fof(c_0_35, plain, ![X35]:(~l1_pre_topc(X35)|m1_pre_topc(X35,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.19/0.38  cnf(c_0_37, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_38, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_39, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  fof(c_0_40, plain, ![X20, X21, X22, X23, X24]:(((v1_funct_1(k2_partfun1(X20,X23,X24,X21))|(~r1_tarski(X21,X20)|~r1_tarski(k7_relset_1(X20,X23,X24,X21),X22))|(~v1_funct_1(X24)|~v1_funct_2(X24,X20,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X23))))|v1_xboole_0(X23))&(v1_funct_2(k2_partfun1(X20,X23,X24,X21),X21,X22)|(~r1_tarski(X21,X20)|~r1_tarski(k7_relset_1(X20,X23,X24,X21),X22))|(~v1_funct_1(X24)|~v1_funct_2(X24,X20,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X23))))|v1_xboole_0(X23)))&(m1_subset_1(k2_partfun1(X20,X23,X24,X21),k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|(~r1_tarski(X21,X20)|~r1_tarski(k7_relset_1(X20,X23,X24,X21),X22))|(~v1_funct_1(X24)|~v1_funct_2(X24,X20,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X23))))|v1_xboole_0(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t178_funct_2])])])])])).
% 0.19/0.38  cnf(c_0_41, plain, (r1_tarski(k9_relat_1(X1,X2),X3)|~v1_funct_2(X1,X4,X3)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  fof(c_0_42, plain, ![X36, X37, X38]:((~r1_tarski(u1_struct_0(X37),u1_struct_0(X38))|m1_pre_topc(X37,X38)|~m1_pre_topc(X38,X36)|~m1_pre_topc(X37,X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(~m1_pre_topc(X37,X38)|r1_tarski(u1_struct_0(X37),u1_struct_0(X38))|~m1_pre_topc(X38,X36)|~m1_pre_topc(X37,X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.19/0.38  cnf(c_0_43, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_22]), c_0_16])])).
% 0.19/0.38  cnf(c_0_45, plain, (k7_relset_1(X1,X2,k7_relat_1(X3,X4),X5)=k9_relat_1(X3,X5)|~m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X5,X4)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_16])).
% 0.19/0.38  cnf(c_0_48, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|v1_xboole_0(X2)|~r1_tarski(X4,X1)|~r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(k9_relat_1(esk4_0,X1),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_16]), c_0_21]), c_0_22])])).
% 0.19/0.38  cnf(c_0_50, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (m1_pre_topc(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_20])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (k9_relat_1(esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)|~m1_subset_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),X2)|~r1_tarski(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_16]), c_0_21]), c_0_22])])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (r1_tarski(k7_relset_1(X1,X2,esk4_0,X3),u1_struct_0(esk1_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_18]), c_0_20])])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (k9_relat_1(esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)|~m1_subset_1(k2_partfun1(X1,X2,esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_37]), c_0_22])])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk1_0))))|~r1_tarski(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_16])])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_55, c_0_29])).
% 0.19/0.38  fof(c_0_59, plain, ![X30]:(v2_struct_0(X30)|~l1_struct_0(X30)|~v1_xboole_0(u1_struct_0(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.38  fof(c_0_60, plain, ![X29]:(~l1_pre_topc(X29)|l1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (k7_relset_1(X1,X2,esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)|~m1_subset_1(k2_partfun1(X3,X4,esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_56, c_0_34])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.38  cnf(c_0_63, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.38  cnf(c_0_64, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|k7_relset_1(X1,X2,esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_16])])).
% 0.19/0.38  cnf(c_0_66, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_65, c_0_16])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_19])]), c_0_23]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 69
% 0.19/0.38  # Proof object clause steps            : 44
% 0.19/0.38  # Proof object formula steps           : 25
% 0.19/0.38  # Proof object conjectures             : 33
% 0.19/0.38  # Proof object clause conjectures      : 30
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 23
% 0.19/0.38  # Proof object initial formulas used   : 12
% 0.19/0.38  # Proof object generating inferences   : 21
% 0.19/0.38  # Proof object simplifying inferences  : 35
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 12
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 28
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 28
% 0.19/0.38  # Processed clauses                    : 174
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 53
% 0.19/0.38  # ...remaining for further processing  : 121
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 2
% 0.19/0.38  # Backward-rewritten                   : 24
% 0.19/0.38  # Generated clauses                    : 234
% 0.19/0.38  # ...of the previous two non-trivial   : 227
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 234
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 67
% 0.19/0.38  #    Positive orientable unit clauses  : 18
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 6
% 0.19/0.38  #    Non-unit-clauses                  : 43
% 0.19/0.38  # Current number of unprocessed clauses: 107
% 0.19/0.38  # ...number of literals in the above   : 514
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 54
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1041
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 417
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 54
% 0.19/0.38  # Unit Clause-clause subsumption calls : 21
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 1
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 9304
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.038 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.044 s
% 0.19/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
