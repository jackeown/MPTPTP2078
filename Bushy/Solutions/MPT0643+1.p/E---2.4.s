%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t50_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:24 EDT 2019

% Result     : Theorem 14.63s
% Output     : CNFRefutation 14.63s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 157 expanded)
%              Number of clauses        :   32 (  53 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  241 (1129 expanded)
%              Number of equality atoms :   65 ( 424 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t50_funct_1.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t50_funct_1.p',t3_subset)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t50_funct_1.p',d5_funct_1)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t50_funct_1.p',t34_funct_1)).

fof(t50_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = X1
              & k1_relat_1(X3) = X1
              & r1_tarski(k2_relat_1(X3),X1)
              & v2_funct_1(X2)
              & k5_relat_1(X3,X2) = X2 )
           => X3 = k6_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t50_funct_1.p',t50_funct_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t50_funct_1.p',t7_boole)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t50_funct_1.p',t23_funct_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t50_funct_1.p',t2_subset)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t50_funct_1.p',d8_funct_1)).

fof(c_0_9,plain,(
    ! [X43,X44,X45] :
      ( ~ r2_hidden(X43,X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(X45))
      | m1_subset_1(X43,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_10,plain,(
    ! [X41,X42] :
      ( ( ~ m1_subset_1(X41,k1_zfmisc_1(X42))
        | r1_tarski(X41,X42) )
      & ( ~ r1_tarski(X41,X42)
        | m1_subset_1(X41,k1_zfmisc_1(X42)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X14,X15,X16,X18] :
      ( ( r2_hidden(esk4_3(X10,X11,X12),k1_relat_1(X10))
        | ~ r2_hidden(X12,X11)
        | X11 != k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X12 = k1_funct_1(X10,esk4_3(X10,X11,X12))
        | ~ r2_hidden(X12,X11)
        | X11 != k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(X15,k1_relat_1(X10))
        | X14 != k1_funct_1(X10,X15)
        | r2_hidden(X14,X11)
        | X11 != k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(esk5_2(X10,X16),X16)
        | ~ r2_hidden(X18,k1_relat_1(X10))
        | esk5_2(X10,X16) != k1_funct_1(X10,X18)
        | X16 = k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk6_2(X10,X16),k1_relat_1(X10))
        | r2_hidden(esk5_2(X10,X16),X16)
        | X16 = k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk5_2(X10,X16) = k1_funct_1(X10,esk6_2(X10,X16))
        | r2_hidden(esk5_2(X10,X16),X16)
        | X16 = k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_12,plain,(
    ! [X37,X38,X39] :
      ( ( k1_relat_1(X38) = X37
        | X38 != k6_relat_1(X37)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( ~ r2_hidden(X39,X37)
        | k1_funct_1(X38,X39) = X39
        | X38 != k6_relat_1(X37)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( r2_hidden(esk10_2(X37,X38),X37)
        | k1_relat_1(X38) != X37
        | X38 = k6_relat_1(X37)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( k1_funct_1(X38,esk10_2(X37,X38)) != esk10_2(X37,X38)
        | k1_relat_1(X38) != X37
        | X38 = k6_relat_1(X37)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( ( k1_relat_1(X2) = X1
                & k1_relat_1(X3) = X1
                & r1_tarski(k2_relat_1(X3),X1)
                & v2_funct_1(X2)
                & k5_relat_1(X3,X2) = X2 )
             => X3 = k6_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_funct_1])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k1_relat_1(esk2_0) = esk1_0
    & k1_relat_1(esk3_0) = esk1_0
    & r1_tarski(k2_relat_1(esk3_0),esk1_0)
    & v2_funct_1(esk2_0)
    & k5_relat_1(esk3_0,esk2_0) = esk2_0
    & esk3_0 != k6_relat_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

fof(c_0_21,plain,(
    ! [X50,X51] :
      ( ~ r2_hidden(X50,X51)
      | ~ v1_xboole_0(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_22,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk10_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 != k6_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | ~ r2_hidden(X32,k1_relat_1(X33))
      | k1_funct_1(k5_relat_1(X33,X34),X32) = k1_funct_1(X34,k1_funct_1(X33,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

fof(c_0_28,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X35,X36)
      | v1_xboole_0(X36)
      | r2_hidden(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk10_2(esk1_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_33,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v2_funct_1(X20)
        | ~ r2_hidden(X21,k1_relat_1(X20))
        | ~ r2_hidden(X22,k1_relat_1(X20))
        | k1_funct_1(X20,X21) != k1_funct_1(X20,X22)
        | X21 = X22
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( r2_hidden(esk7_1(X20),k1_relat_1(X20))
        | v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( r2_hidden(esk8_1(X20),k1_relat_1(X20))
        | v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( k1_funct_1(X20,esk7_1(X20)) = k1_funct_1(X20,esk8_1(X20))
        | v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( esk7_1(X20) != esk8_1(X20)
        | v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_34,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k5_relat_1(esk3_0,esk2_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k1_funct_1(esk3_0,X1),esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk2_0,k1_funct_1(esk3_0,X1)) = k1_funct_1(esk2_0,X1)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_23]),c_0_36]),c_0_24]),c_0_37]),c_0_25])])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,X1),esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_46,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk10_2(X2,X1)) != esk10_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = X2
    | k1_funct_1(esk2_0,X1) != k1_funct_1(esk2_0,X2)
    | ~ r2_hidden(X2,esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_36]),c_0_37])]),c_0_45])).

cnf(c_0_48,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk10_2(k1_relat_1(X1),X1)) != esk10_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = X1
    | ~ r2_hidden(X1,esk1_0) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_23]),c_0_24]),c_0_25]),c_0_23]),c_0_32])]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
