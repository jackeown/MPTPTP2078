%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t11_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:12 EDT 2019

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 387 expanded)
%              Number of clauses        :   41 ( 206 expanded)
%              Number of leaves         :   13 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          :  189 (1415 expanded)
%              Number of equality atoms :   80 ( 648 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',t6_boole)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',t7_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',d3_tarski)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',dt_o_0_0_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',t3_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',existence_m1_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',d1_setfam_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',d1_tarski)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',t5_subset)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t11_setfam_1.p',t11_setfam_1)).

fof(c_0_11,plain,(
    ! [X52] :
      ( ~ v1_xboole_0(X52)
      | X52 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_12,plain,(
    ! [X53,X54] :
      ( ~ r2_hidden(X53,X54)
      | ~ v1_xboole_0(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_13,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ( ~ r1_tarski(X30,X31)
        | ~ r2_hidden(X32,X30)
        | r2_hidden(X32,X31) )
      & ( r2_hidden(esk6_2(X33,X34),X33)
        | r1_tarski(X33,X34) )
      & ( ~ r2_hidden(esk6_2(X33,X34),X34)
        | r1_tarski(X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_18])).

fof(c_0_22,plain,(
    ! [X42,X43] :
      ( ( ~ m1_subset_1(X42,k1_zfmisc_1(X43))
        | r1_tarski(X42,X43) )
      & ( ~ r1_tarski(X42,X43)
        | m1_subset_1(X42,k1_zfmisc_1(X43)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_23,plain,(
    ! [X36] : m1_subset_1(esk7_1(X36),X36) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_24,plain,(
    ! [X10,X11,X12,X13,X14,X16,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X12,X11)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X12,X13)
        | X11 != k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( r2_hidden(esk2_3(X10,X11,X14),X10)
        | r2_hidden(X14,X11)
        | X11 != k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( ~ r2_hidden(X14,esk2_3(X10,X11,X14))
        | r2_hidden(X14,X11)
        | X11 != k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X10,X16),X10)
        | ~ r2_hidden(esk3_2(X10,X16),X16)
        | X16 = k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( ~ r2_hidden(esk3_2(X10,X16),esk4_2(X10,X16))
        | ~ r2_hidden(esk3_2(X10,X16),X16)
        | X16 = k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X10,X16),X16)
        | ~ r2_hidden(X19,X10)
        | r2_hidden(esk3_2(X10,X16),X19)
        | X16 = k1_setfam_1(X10)
        | X10 = k1_xboole_0 )
      & ( X21 != k1_setfam_1(X20)
        | X21 = k1_xboole_0
        | X20 != k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | X22 = k1_setfam_1(X20)
        | X20 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X23
        | X24 != k1_tarski(X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k1_tarski(X23) )
      & ( ~ r2_hidden(esk5_2(X27,X28),X28)
        | esk5_2(X27,X28) != X27
        | X28 = k1_tarski(X27) )
      & ( r2_hidden(esk5_2(X27,X28),X28)
        | esk5_2(X27,X28) = X27
        | X28 = k1_tarski(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_30,plain,
    ( X1 = k1_setfam_1(X2)
    | X1 != k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(esk7_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | ~ v1_xboole_0(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k1_setfam_1(X1),X2)
    | esk7_1(X2) != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_36,plain,
    ( esk7_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_40,plain,
    ( ~ epred58_0
  <=> ! [X2] : X2 != k1_xboole_0 ),
    introduced(definition)).

fof(c_0_41,plain,
    ( ~ epred57_0
  <=> ! [X1] : k1_tarski(X1) != k1_xboole_0 ),
    introduced(definition)).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_21])])).

cnf(c_0_44,plain,
    ( epred58_0
    | X1 != k1_xboole_0 ),
    inference(split_equiv,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( ~ epred58_0
    | ~ epred57_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_30]),c_0_43]),c_0_41]),c_0_40])).

cnf(c_0_46,plain,
    ( epred58_0 ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_47,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(esk3_2(X1,X2),X3)
    | X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_48,plain,
    ( ~ epred57_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_49,plain,
    ( X1 = k1_setfam_1(k1_tarski(X2))
    | k1_tarski(X2) = k1_xboole_0
    | r2_hidden(esk3_2(k1_tarski(X2),X1),X1)
    | r2_hidden(esk3_2(k1_tarski(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

cnf(c_0_50,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_41]),c_0_48])).

cnf(c_0_51,plain,
    ( X1 = k1_setfam_1(k1_tarski(X2))
    | r2_hidden(esk3_2(k1_tarski(X2),X1),X2)
    | r2_hidden(esk3_2(k1_tarski(X2),X1),X1) ),
    inference(sr,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_52,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_53,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1
    | r2_hidden(esk3_2(k1_tarski(X1),X1),X1) ),
    inference(ef,[status(thm)],[c_0_51])).

fof(c_0_55,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_56,plain,
    ( X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1
    | r2_hidden(esk4_2(k1_tarski(X1),X1),k1_tarski(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_50])).

fof(c_0_59,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_55])])])).

cnf(c_0_60,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1
    | ~ r2_hidden(esk3_2(k1_tarski(X1),X1),esk4_2(k1_tarski(X1),X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_54]),c_0_50])).

cnf(c_0_61,plain,
    ( esk4_2(k1_tarski(X1),X1) = X1
    | k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_63,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
