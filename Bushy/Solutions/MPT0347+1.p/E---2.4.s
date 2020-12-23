%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t17_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:21 EDT 2019

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 469 expanded)
%              Number of clauses        :   78 ( 230 expanded)
%              Number of leaves         :   11 ( 118 expanded)
%              Depth                    :   22
%              Number of atoms          :  299 (2154 expanded)
%              Number of equality atoms :   44 ( 385 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',d5_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t6_boole)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t7_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',dt_o_0_0_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t4_boole)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',dt_k7_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',redefinition_k7_subset_1)).

fof(t17_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(X5,X2)
                    <=> ( r2_hidden(X5,X3)
                        & ~ r2_hidden(X5,X4) ) ) )
               => X2 = k7_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t17_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',t7_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',existence_m1_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t17_subset_1.p',d10_xboole_0)).

fof(c_0_11,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk5_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk5_3(X20,X21,X22),X20)
        | r2_hidden(esk5_3(X20,X21,X22),X21)
        | X22 = k4_xboole_0(X20,X21) )
      & ( r2_hidden(esk5_3(X20,X21,X22),X20)
        | r2_hidden(esk5_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk5_3(X20,X21,X22),X21)
        | r2_hidden(esk5_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_12,plain,(
    ! [X34] :
      ( ~ v1_xboole_0(X34)
      | X34 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_13,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X35,X36)
      | ~ v1_xboole_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X33] : k4_xboole_0(k1_xboole_0,X33) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_xboole_0(k4_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_21])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | m1_subset_1(k7_subset_1(X24,X25,X26),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

fof(c_0_28,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | k7_subset_1(X29,X30,X31) = k4_xboole_0(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_25])]),c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,X2)
                      <=> ( r2_hidden(X5,X3)
                          & ~ r2_hidden(X5,X4) ) ) )
                 => X2 = k7_subset_1(X1,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_subset_1])).

fof(c_0_32,plain,(
    ! [X37,X38,X39] :
      ( ( m1_subset_1(esk7_3(X37,X38,X39),X37)
        | r1_tarski(X38,X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(X37)) )
      & ( r2_hidden(esk7_3(X37,X38,X39),X38)
        | r1_tarski(X38,X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(X37)) )
      & ( ~ r2_hidden(esk7_3(X37,X38,X39),X39)
        | r1_tarski(X38,X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk5_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_37,negated_conjecture,(
    ! [X10] :
      ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
      & ( r2_hidden(X10,esk3_0)
        | ~ r2_hidden(X10,esk2_0)
        | ~ m1_subset_1(X10,esk1_0) )
      & ( ~ r2_hidden(X10,esk4_0)
        | ~ r2_hidden(X10,esk2_0)
        | ~ m1_subset_1(X10,esk1_0) )
      & ( ~ r2_hidden(X10,esk3_0)
        | r2_hidden(X10,esk4_0)
        | r2_hidden(X10,esk2_0)
        | ~ m1_subset_1(X10,esk1_0) )
      & esk2_0 != k7_subset_1(esk1_0,esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_29])).

fof(c_0_42,plain,(
    ! [X27] : m1_subset_1(esk6_1(X27),X27) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_39])).

cnf(c_0_48,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk7_3(esk1_0,X1,X2),esk2_0)
    | ~ r2_hidden(esk7_3(esk1_0,X1,X2),esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | r2_hidden(esk7_3(X4,X1,k4_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk7_3(X4,X1,k4_xboole_0(X2,X3)),X2)
    | ~ m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_20])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | r2_hidden(esk7_3(X4,k4_xboole_0(X1,X2),X3),X1)
    | ~ m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_40])).

cnf(c_0_55,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_57,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r2_hidden(esk7_3(esk1_0,esk4_0,X1),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_39]),c_0_51])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk7_3(X3,X1,k4_xboole_0(X1,X2)),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_39]),c_0_40])).

cnf(c_0_60,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_53]),c_0_40])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_25])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_63,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk7_3(X4,k4_xboole_0(X1,X2),X3),X2)
    | ~ m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk7_3(esk1_0,X1,X2),esk3_0)
    | ~ r2_hidden(esk7_3(esk1_0,X1,X2),esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_44])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk4_0,k4_xboole_0(esk4_0,esk2_0))
    | ~ m1_subset_1(k4_xboole_0(esk4_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_51])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk3_0),X2)
    | ~ r2_hidden(esk7_3(esk1_0,k4_xboole_0(X1,esk3_0),X2),esk2_0)
    | ~ m1_subset_1(k4_xboole_0(X1,esk3_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0
    | ~ m1_subset_1(k4_xboole_0(esk4_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk2_0,X1) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(esk2_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk3_0),X1)
    | ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_53])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_40]),c_0_51])])).

cnf(c_0_74,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk5_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_30])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k1_xboole_0
    | ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_55])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_73])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk5_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_40]),c_0_62])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(X1,esk4_0) = X1
    | ~ r2_hidden(esk5_3(X1,esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_79]),c_0_29])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk7_3(esk1_0,X1,X2),esk4_0)
    | r2_hidden(esk7_3(esk1_0,X1,X2),esk2_0)
    | ~ r2_hidden(esk7_3(esk1_0,X1,X2),esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_44])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(esk3_0,X2))
    | r2_hidden(esk7_3(X3,X1,k4_xboole_0(esk3_0,X2)),X2)
    | ~ r2_hidden(esk7_3(X3,X1,k4_xboole_0(esk3_0,X2)),esk2_0)
    | ~ m1_subset_1(k4_xboole_0(esk3_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk4_0),X2)
    | r2_hidden(esk7_3(esk1_0,k4_xboole_0(X1,esk4_0),X2),esk2_0)
    | ~ r2_hidden(esk7_3(esk1_0,k4_xboole_0(X1,esk4_0),X2),esk3_0)
    | ~ m1_subset_1(k4_xboole_0(X1,esk4_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r2_hidden(esk7_3(X2,esk2_0,X1),esk4_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,X1))
    | r2_hidden(esk7_3(X2,esk2_0,k4_xboole_0(esk3_0,X1)),X1)
    | ~ m1_subset_1(k4_xboole_0(esk3_0,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_39])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk4_0),X1)
    | r2_hidden(esk7_3(esk1_0,k4_xboole_0(esk3_0,esk4_0),X1),esk2_0)
    | ~ m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_53])).

cnf(c_0_90,negated_conjecture,
    ( esk2_0 != k7_subset_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))
    | ~ m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_89]),c_0_62])])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_34]),c_0_91])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_40])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))
    | ~ m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_93]),c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_91]),c_0_62])])).

cnf(c_0_98,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_40]),c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
