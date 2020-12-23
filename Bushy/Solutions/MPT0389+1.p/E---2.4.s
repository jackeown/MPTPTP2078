%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t7_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:20 EDT 2019

% Result     : Theorem 170.83s
% Output     : CNFRefutation 170.83s
% Verified   : 
% Statistics : Number of formulae       :  117 (2775 expanded)
%              Number of clauses        :   89 (1399 expanded)
%              Number of leaves         :   14 ( 716 expanded)
%              Depth                    :   32
%              Number of atoms          :  349 (7996 expanded)
%              Number of equality atoms :   63 (2134 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t7_setfam_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t8_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',d3_tarski)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',existence_m1_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t6_boole)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',d1_setfam_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',dt_o_0_0_xboole_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t1_subset)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',antisymmetry_r2_hidden)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t7_boole)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t5_subset)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => ( X1 = k1_xboole_0
          | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t7_setfam_1])).

fof(c_0_15,plain,(
    ! [X45,X46] :
      ( ~ v1_xboole_0(X45)
      | X45 = X46
      | ~ v1_xboole_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_16,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X32,X33)
      | v1_xboole_0(X33)
      | r2_hidden(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_17,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | m1_subset_1(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_18,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( ~ r1_tarski(X22,X23)
        | ~ r2_hidden(X24,X22)
        | r2_hidden(X24,X23) )
      & ( r2_hidden(esk6_2(X25,X26),X25)
        | r1_tarski(X25,X26) )
      & ( ~ r2_hidden(esk6_2(X25,X26),X26)
        | r1_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & esk1_0 != k1_xboole_0
    & ~ r1_tarski(k1_setfam_1(esk2_0),k1_setfam_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X28] : m1_subset_1(esk7_1(X28),X28) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_24,plain,(
    ! [X42] :
      ( ~ v1_xboole_0(X42)
      | X42 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_25,plain,(
    ! [X9,X10,X11,X12,X13,X15,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X11,X10)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X11,X12)
        | X10 != k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( r2_hidden(esk3_3(X9,X10,X13),X9)
        | r2_hidden(X13,X10)
        | X10 != k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( ~ r2_hidden(X13,esk3_3(X9,X10,X13))
        | r2_hidden(X13,X10)
        | X10 != k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( r2_hidden(esk5_2(X9,X15),X9)
        | ~ r2_hidden(esk4_2(X9,X15),X15)
        | X15 = k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( ~ r2_hidden(esk4_2(X9,X15),esk5_2(X9,X15))
        | ~ r2_hidden(esk4_2(X9,X15),X15)
        | X15 = k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X9,X15),X15)
        | ~ r2_hidden(X18,X9)
        | r2_hidden(esk4_2(X9,X15),X18)
        | X15 = k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( X20 != k1_setfam_1(X19)
        | X20 = k1_xboole_0
        | X19 != k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | X21 = k1_setfam_1(X19)
        | X19 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( X1 = X2
    | r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( X1 = X2
    | r2_hidden(esk7_1(X2),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,esk1_0)
    | ~ r1_tarski(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( o_0_0_xboole_0 = X1
    | r2_hidden(esk7_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( esk1_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(rw,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk6_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk7_1(esk1_0),X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_49,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk6_2(k1_setfam_1(X1),X2),X3)
    | r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r2_hidden(esk6_2(X1,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_51,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,esk7_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_48])).

cnf(c_0_53,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk6_2(k1_setfam_1(X1),X2),esk7_1(X1))
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_54,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ m1_subset_1(esk6_2(X1,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk6_2(k1_setfam_1(esk1_0),X1),X2)
    | r1_tarski(k1_setfam_1(esk1_0),X1)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_43])).

fof(c_0_57,plain,(
    ! [X30,X31] :
      ( ~ r2_hidden(X30,X31)
      | m1_subset_1(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk1_0),esk2_0)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk3_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_39])).

fof(c_0_62,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | ~ r2_hidden(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k1_setfam_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_59])).

cnf(c_0_64,plain,
    ( X1 = o_0_0_xboole_0
    | m1_subset_1(esk3_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk3_3(esk1_0,k1_setfam_1(esk1_0),X1),esk1_0)
    | r2_hidden(X1,esk2_0)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_43])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk3_3(esk1_0,k1_setfam_1(esk1_0),X1),esk1_0)
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_68,plain,(
    ! [X43,X44] :
      ( ~ r2_hidden(X43,X44)
      | ~ v1_xboole_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk3_3(esk1_0,k1_setfam_1(esk1_0),esk2_0),esk1_0)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( X1 = esk1_0
    | r2_hidden(esk3_3(esk1_0,k1_setfam_1(esk1_0),esk2_0),esk1_0)
    | ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_69])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_45])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_0,k1_setfam_1(esk1_0),esk2_0),esk1_0)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_33]),c_0_43])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_22])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_73])).

cnf(c_0_76,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk6_2(k1_setfam_1(X1),X2),X3)
    | r1_tarski(k1_setfam_1(X1),X2)
    | ~ m1_subset_1(X3,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_51])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,X2)
    | r1_tarski(X3,X4)
    | ~ m1_subset_1(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_22])).

cnf(c_0_79,plain,
    ( X1 = o_0_0_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_76])).

cnf(c_0_80,plain,
    ( m1_subset_1(esk7_1(X1),X2)
    | r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_31])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(X1,esk1_0)
    | ~ m1_subset_1(esk6_2(X1,esk1_0),esk1_0)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_78])).

cnf(c_0_82,plain,
    ( X1 = o_0_0_xboole_0
    | r1_tarski(k1_setfam_1(X1),esk7_1(X2))
    | r1_tarski(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk1_0),esk1_0)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_56])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk1_0),esk7_1(k1_setfam_1(esk1_0)))
    | r1_tarski(k1_setfam_1(esk1_0),X1)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_43])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk1_0),esk7_1(k1_setfam_1(esk1_0)))
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(ef,[status(thm)],[c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(X1,esk7_1(k1_setfam_1(esk1_0)))
    | ~ r2_hidden(X1,k1_setfam_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_85])).

fof(c_0_87,plain,(
    ! [X39,X40,X41] :
      ( ~ r2_hidden(X39,X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(X41))
      | ~ v1_xboole_0(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(esk7_1(k1_setfam_1(esk1_0)),X1)
    | ~ r2_hidden(X1,k1_setfam_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_86])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(esk7_1(k1_setfam_1(esk1_0)),k1_setfam_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_86])).

cnf(c_0_91,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_27])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk1_0),X1)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_74]),c_0_31])])).

cnf(c_0_93,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0))
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_73])).

cnf(c_0_94,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk7_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_31])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0))
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_93,c_0_22])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_setfam_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0))
    | ~ r1_tarski(esk1_0,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_91,c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_36])).

cnf(c_0_100,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk3_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_hidden(X1,k1_setfam_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_33])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,X4)
    | ~ m1_subset_1(X1,X2)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0))
    | ~ r1_tarski(esk1_0,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_22])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(esk3_3(esk1_0,k1_setfam_1(esk1_0),X1),esk2_0)
    | r2_hidden(X1,k1_setfam_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_61]),c_0_43])).

cnf(c_0_104,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk3_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | r2_hidden(esk6_2(k1_setfam_1(esk2_0),X1),X2)
    | r1_tarski(k1_setfam_1(esk2_0),X1)
    | ~ r2_hidden(X2,esk1_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_36])).

cnf(c_0_106,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_setfam_1(esk1_0))
    | ~ m1_subset_1(X2,X3)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0))
    | ~ r1_tarski(X3,k1_setfam_1(esk1_0))
    | ~ r1_tarski(esk1_0,X3) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk3_3(esk1_0,k1_setfam_1(esk1_0),X1),esk2_0)
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_103])).

cnf(c_0_108,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk3_3(X1,k1_setfam_1(X1),X2)) ),
    inference(rw,[status(thm)],[c_0_104,c_0_39])).

cnf(c_0_109,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | r2_hidden(esk6_2(k1_setfam_1(esk2_0),X1),esk3_3(esk1_0,k1_setfam_1(esk1_0),X2))
    | r2_hidden(X2,k1_setfam_1(esk1_0))
    | r1_tarski(k1_setfam_1(esk2_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_61]),c_0_43])).

cnf(c_0_110,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_setfam_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_setfam_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_29])])).

cnf(c_0_111,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | r2_hidden(esk6_2(k1_setfam_1(esk2_0),X1),k1_setfam_1(esk1_0))
    | r1_tarski(k1_setfam_1(esk2_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_43])).

cnf(c_0_112,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk2_0),k1_setfam_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_113,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k1_zfmisc_1(esk1_0))
    | ~ r1_tarski(esk2_0,k1_setfam_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_48])).

cnf(c_0_114,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_111]),c_0_112])).

cnf(c_0_115,plain,
    ( r1_tarski(o_0_0_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_33])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114]),c_0_115]),c_0_114]),c_0_115])]),
    [proof]).
%------------------------------------------------------------------------------
