%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:50 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 193 expanded)
%              Number of clauses        :   40 (  84 expanded)
%              Number of leaves         :    9 (  47 expanded)
%              Depth                    :   18
%              Number of atoms          :  206 ( 778 expanded)
%              Number of equality atoms :   19 (  56 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t35_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(d5_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(cc1_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(c_0_9,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_10,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | ~ v1_xboole_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_17,plain,(
    ! [X12,X13,X14] :
      ( ( m1_subset_1(esk1_3(X12,X13,X14),X12)
        | r1_tarski(X13,X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r1_tarski(X13,X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | r1_tarski(X13,X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

fof(c_0_18,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_19,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => v2_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t35_tex_2])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_21])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v1_xboole_0(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk6_0,k3_xboole_0(X1,X2))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k3_xboole_0(esk6_0,X1) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_16])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_28])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_37,plain,(
    ! [X25,X26,X27,X30] :
      ( ( m1_subset_1(esk3_3(X25,X26,X27),k1_zfmisc_1(u1_struct_0(X25)))
        | ~ r1_tarski(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( v3_pre_topc(esk3_3(X25,X26,X27),X25)
        | ~ r1_tarski(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( k9_subset_1(u1_struct_0(X25),X26,esk3_3(X25,X26,X27)) = X27
        | ~ r1_tarski(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk4_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))
        | v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( r1_tarski(esk4_2(X25,X26),X26)
        | v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) )
      & ( ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ v3_pre_topc(X30,X25)
        | k9_subset_1(u1_struct_0(X25),X26,X30) != esk4_2(X25,X26)
        | v2_tex_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_40,plain,
    ( r1_tarski(esk4_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_38])).

cnf(c_0_42,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_44,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | k9_subset_1(X9,X10,X11) = k3_xboole_0(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_45,plain,
    ( esk4_2(X1,X2) = X2
    | v2_tex_2(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk4_2(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( v2_tex_2(X1,esk5_0)
    | m1_subset_1(esk6_0,k1_zfmisc_1(esk4_2(esk5_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_48,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_49,plain,(
    ! [X21,X22] :
      ( ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ v1_xboole_0(X22)
      | v3_pre_topc(X22,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).

cnf(c_0_50,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk4_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( esk4_2(esk5_0,esk6_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_43]),c_0_35])]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k9_subset_1(X1,esk6_0,X2) = esk6_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_32])).

cnf(c_0_53,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_43]),c_0_35])]),c_0_47]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(X1,esk5_0)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_43])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_35]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:12:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.41  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.22/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.22/0.41  #
% 0.22/0.41  # Preprocessing time       : 0.028 s
% 0.22/0.41  # Presaturation interreduction done
% 0.22/0.41  
% 0.22/0.41  # Proof found!
% 0.22/0.41  # SZS status Theorem
% 0.22/0.41  # SZS output start CNFRefutation
% 0.22/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.22/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.22/0.41  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.22/0.41  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 0.22/0.41  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.22/0.41  fof(t35_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 0.22/0.41  fof(d5_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 0.22/0.41  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.22/0.41  fof(cc1_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 0.22/0.41  fof(c_0_9, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.22/0.41  fof(c_0_10, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.22/0.41  cnf(c_0_11, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.41  fof(c_0_12, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|~v1_xboole_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.22/0.41  cnf(c_0_13, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.41  cnf(c_0_14, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_11])).
% 0.22/0.41  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.41  cnf(c_0_16, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.22/0.41  fof(c_0_17, plain, ![X12, X13, X14]:((m1_subset_1(esk1_3(X12,X13,X14),X12)|r1_tarski(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(X12)))&((r2_hidden(esk1_3(X12,X13,X14),X13)|r1_tarski(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(X12)))&(~r2_hidden(esk1_3(X12,X13,X14),X14)|r1_tarski(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.22/0.41  fof(c_0_18, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.22/0.41  cnf(c_0_19, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.22/0.41  cnf(c_0_20, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.22/0.41  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.41  fof(c_0_22, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t35_tex_2])).
% 0.22/0.41  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.22/0.41  cnf(c_0_24, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_13, c_0_21])).
% 0.22/0.41  fof(c_0_25, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&~v2_tex_2(esk6_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.22/0.41  cnf(c_0_26, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.41  cnf(c_0_27, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.22/0.41  cnf(c_0_28, negated_conjecture, (v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.22/0.41  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 0.22/0.41  cnf(c_0_30, negated_conjecture, (r1_tarski(esk6_0,k3_xboole_0(X1,X2))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.22/0.41  cnf(c_0_31, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_15, c_0_24])).
% 0.22/0.41  cnf(c_0_32, negated_conjecture, (k3_xboole_0(esk6_0,X1)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_16])])).
% 0.22/0.41  cnf(c_0_33, negated_conjecture, (~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_28])])).
% 0.22/0.41  cnf(c_0_34, negated_conjecture, (r1_tarski(esk6_0,X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_33, c_0_20])).
% 0.22/0.41  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.22/0.41  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.41  fof(c_0_37, plain, ![X25, X26, X27, X30]:(((m1_subset_1(esk3_3(X25,X26,X27),k1_zfmisc_1(u1_struct_0(X25)))|~r1_tarski(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|~v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_pre_topc(X25))&((v3_pre_topc(esk3_3(X25,X26,X27),X25)|~r1_tarski(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|~v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_pre_topc(X25))&(k9_subset_1(u1_struct_0(X25),X26,esk3_3(X25,X26,X27))=X27|~r1_tarski(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|~v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_pre_topc(X25))))&((m1_subset_1(esk4_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))|v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_pre_topc(X25))&((r1_tarski(esk4_2(X25,X26),X26)|v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_pre_topc(X25))&(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X25)))|(~v3_pre_topc(X30,X25)|k9_subset_1(u1_struct_0(X25),X26,X30)!=esk4_2(X25,X26))|v2_tex_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~l1_pre_topc(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).
% 0.22/0.41  cnf(c_0_38, negated_conjecture, (r1_tarski(esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.22/0.41  cnf(c_0_39, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 0.22/0.41  cnf(c_0_40, plain, (r1_tarski(esk4_2(X1,X2),X2)|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.22/0.41  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_13, c_0_38])).
% 0.22/0.41  cnf(c_0_42, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.22/0.41  cnf(c_0_43, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.22/0.41  fof(c_0_44, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X9))|k9_subset_1(X9,X10,X11)=k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.22/0.41  cnf(c_0_45, plain, (esk4_2(X1,X2)=X2|v2_tex_2(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(esk4_2(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.22/0.41  cnf(c_0_46, negated_conjecture, (v2_tex_2(X1,esk5_0)|m1_subset_1(esk6_0,k1_zfmisc_1(esk4_2(esk5_0,X1)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.22/0.41  cnf(c_0_47, negated_conjecture, (~v2_tex_2(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.22/0.41  cnf(c_0_48, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.22/0.41  fof(c_0_49, plain, ![X21, X22]:(~v2_pre_topc(X21)|~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v1_xboole_0(X22)|v3_pre_topc(X22,X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).
% 0.22/0.41  cnf(c_0_50, plain, (v2_tex_2(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=esk4_2(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.22/0.41  cnf(c_0_51, negated_conjecture, (esk4_2(esk5_0,esk6_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_43]), c_0_35])]), c_0_47])).
% 0.22/0.41  cnf(c_0_52, negated_conjecture, (k9_subset_1(X1,esk6_0,X2)=esk6_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_32])).
% 0.22/0.41  cnf(c_0_53, plain, (v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.22/0.41  cnf(c_0_54, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.22/0.41  cnf(c_0_55, negated_conjecture, (~v3_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_43]), c_0_35])]), c_0_47]), c_0_52])).
% 0.22/0.41  cnf(c_0_56, negated_conjecture, (v3_pre_topc(X1,esk5_0)|~v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_43])])).
% 0.22/0.41  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.22/0.41  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_35]), c_0_28])]), ['proof']).
% 0.22/0.41  # SZS output end CNFRefutation
% 0.22/0.41  # Proof object total steps             : 59
% 0.22/0.41  # Proof object clause steps            : 40
% 0.22/0.41  # Proof object formula steps           : 19
% 0.22/0.41  # Proof object conjectures             : 21
% 0.22/0.41  # Proof object clause conjectures      : 18
% 0.22/0.41  # Proof object formula conjectures     : 3
% 0.22/0.41  # Proof object initial clauses used    : 17
% 0.22/0.41  # Proof object initial formulas used   : 9
% 0.22/0.41  # Proof object generating inferences   : 22
% 0.22/0.41  # Proof object simplifying inferences  : 20
% 0.22/0.41  # Training examples: 0 positive, 0 negative
% 0.22/0.41  # Parsed axioms                        : 10
% 0.22/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.41  # Initial clauses                      : 26
% 0.22/0.41  # Removed in clause preprocessing      : 0
% 0.22/0.41  # Initial clauses in saturation        : 26
% 0.22/0.41  # Processed clauses                    : 263
% 0.22/0.41  # ...of these trivial                  : 1
% 0.22/0.41  # ...subsumed                          : 101
% 0.22/0.41  # ...remaining for further processing  : 161
% 0.22/0.41  # Other redundant clauses eliminated   : 2
% 0.22/0.41  # Clauses deleted for lack of memory   : 0
% 0.22/0.41  # Backward-subsumed                    : 20
% 0.22/0.41  # Backward-rewritten                   : 15
% 0.22/0.41  # Generated clauses                    : 509
% 0.22/0.41  # ...of the previous two non-trivial   : 418
% 0.22/0.41  # Contextual simplify-reflections      : 3
% 0.22/0.41  # Paramodulations                      : 507
% 0.22/0.41  # Factorizations                       : 0
% 0.22/0.41  # Equation resolutions                 : 2
% 0.22/0.41  # Propositional unsat checks           : 0
% 0.22/0.41  #    Propositional check models        : 0
% 0.22/0.41  #    Propositional check unsatisfiable : 0
% 0.22/0.41  #    Propositional clauses             : 0
% 0.22/0.41  #    Propositional clauses after purity: 0
% 0.22/0.41  #    Propositional unsat core size     : 0
% 0.22/0.41  #    Propositional preprocessing time  : 0.000
% 0.22/0.41  #    Propositional encoding time       : 0.000
% 0.22/0.41  #    Propositional solver time         : 0.000
% 0.22/0.41  #    Success case prop preproc time    : 0.000
% 0.22/0.41  #    Success case prop encoding time   : 0.000
% 0.22/0.41  #    Success case prop solver time     : 0.000
% 0.22/0.41  # Current number of processed clauses  : 99
% 0.22/0.41  #    Positive orientable unit clauses  : 15
% 0.22/0.41  #    Positive unorientable unit clauses: 0
% 0.22/0.41  #    Negative unit clauses             : 3
% 0.22/0.41  #    Non-unit-clauses                  : 81
% 0.22/0.41  # Current number of unprocessed clauses: 177
% 0.22/0.41  # ...number of literals in the above   : 789
% 0.22/0.41  # Current number of archived formulas  : 0
% 0.22/0.41  # Current number of archived clauses   : 60
% 0.22/0.41  # Clause-clause subsumption calls (NU) : 2818
% 0.22/0.41  # Rec. Clause-clause subsumption calls : 1383
% 0.22/0.41  # Non-unit clause-clause subsumptions  : 100
% 0.22/0.41  # Unit Clause-clause subsumption calls : 107
% 0.22/0.41  # Rewrite failures with RHS unbound    : 0
% 0.22/0.41  # BW rewrite match attempts            : 31
% 0.22/0.41  # BW rewrite match successes           : 8
% 0.22/0.41  # Condensation attempts                : 0
% 0.22/0.41  # Condensation successes               : 0
% 0.22/0.41  # Termbank termtop insertions          : 10393
% 0.22/0.41  
% 0.22/0.41  # -------------------------------------------------
% 0.22/0.41  # User time                : 0.047 s
% 0.22/0.41  # System time              : 0.003 s
% 0.22/0.41  # Total time               : 0.051 s
% 0.22/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
