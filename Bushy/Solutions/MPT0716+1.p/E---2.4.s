%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t171_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:19 EDT 2019

% Result     : Theorem 284.80s
% Output     : CNFRefutation 284.80s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 720 expanded)
%              Number of clauses        :   58 ( 269 expanded)
%              Number of leaves         :    9 ( 180 expanded)
%              Depth                    :   15
%              Number of atoms          :  300 (4259 expanded)
%              Number of equality atoms :   20 ( 110 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t171_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
            <=> ( r1_tarski(X3,k1_relat_1(X1))
                & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',t171_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',d3_tarski)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',t21_funct_1)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',d12_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',t3_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',t7_boole)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',existence_m1_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
              <=> ( r1_tarski(X3,k1_relat_1(X1))
                  & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t171_funct_1])).

fof(c_0_10,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( ~ r1_tarski(X23,X24)
        | ~ r2_hidden(X25,X23)
        | r2_hidden(X25,X24) )
      & ( r2_hidden(esk7_2(X26,X27),X26)
        | r1_tarski(X26,X27) )
      & ( ~ r2_hidden(esk7_2(X26,X27),X27)
        | r1_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
      | ~ r1_tarski(esk3_0,k1_relat_1(esk1_0))
      | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) )
    & ( r1_tarski(esk3_0,k1_relat_1(esk1_0))
      | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) )
    & ( r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))
      | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X35,X36,X37] :
      ( ( r2_hidden(X35,k1_relat_1(X37))
        | ~ r2_hidden(X35,k1_relat_1(k5_relat_1(X37,X36)))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( r2_hidden(k1_funct_1(X37,X35),k1_relat_1(X36))
        | ~ r2_hidden(X35,k1_relat_1(k5_relat_1(X37,X36)))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( ~ r2_hidden(X35,k1_relat_1(X37))
        | ~ r2_hidden(k1_funct_1(X37,X35),k1_relat_1(X36))
        | r2_hidden(X35,k1_relat_1(k5_relat_1(X37,X36)))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X11,X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(esk4_4(X11,X12,X13,X14),k1_relat_1(X11))
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X14 = k1_funct_1(X11,esk4_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X17,k1_relat_1(X11))
        | ~ r2_hidden(X17,X12)
        | X16 != k1_funct_1(X11,X17)
        | r2_hidden(X16,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk5_3(X11,X18,X19),X19)
        | ~ r2_hidden(X21,k1_relat_1(X11))
        | ~ r2_hidden(X21,X18)
        | esk5_3(X11,X18,X19) != k1_funct_1(X11,X21)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk6_3(X11,X18,X19),k1_relat_1(X11))
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk6_3(X11,X18,X19),X18)
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk5_3(X11,X18,X19) = k1_funct_1(X11,esk6_3(X11,X18,X19))
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X40,k1_zfmisc_1(X41))
        | r1_tarski(X40,X41) )
      & ( ~ r1_tarski(X40,X41)
        | m1_subset_1(X40,k1_zfmisc_1(X41)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk1_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_13])).

fof(c_0_27,plain,(
    ! [X49,X50] :
      ( ~ r2_hidden(X49,X50)
      | ~ v1_xboole_0(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk2_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r2_hidden(X1,k9_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk1_0))
    | ~ r2_hidden(esk7_2(X1,k1_relat_1(esk1_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(esk4_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk1_0,X1),k1_relat_1(esk2_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19]),c_0_21])]),c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk1_0,esk3_0),k1_zfmisc_1(k1_relat_1(esk2_0)))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_42,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | m1_subset_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_26]),c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk1_0,esk3_0),k1_zfmisc_1(k1_relat_1(esk2_0)))
    | r2_hidden(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_38])).

fof(c_0_46,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X38,X39)
      | v1_xboole_0(X39)
      | r2_hidden(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_48,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_xboole_0(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_50,plain,
    ( X1 = k1_funct_1(X2,esk4_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( ~ m1_subset_1(k9_relat_1(esk1_0,esk3_0),k1_zfmisc_1(k1_relat_1(esk2_0)))
    | ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r2_hidden(esk7_2(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0))),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk1_0,esk3_0),k1_zfmisc_1(k1_relat_1(esk2_0)))
    | ~ v1_xboole_0(k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_19]),c_0_21])]),c_0_49])).

fof(c_0_57,plain,(
    ! [X31] : m1_subset_1(esk8_1(X31),X31) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_58,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_59,plain,
    ( k1_funct_1(X1,esk4_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk1_0,esk3_0),k1_zfmisc_1(k1_relat_1(esk2_0)))
    | m1_subset_1(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_45])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(k9_relat_1(esk1_0,esk3_0),k1_zfmisc_1(k1_relat_1(esk2_0)))
    | ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_40])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_33])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk1_0,esk3_0),k1_zfmisc_1(k1_relat_1(esk2_0)))
    | ~ m1_subset_1(X1,esk3_0)
    | ~ v1_xboole_0(k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_64,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(esk4_4(X3,X4,k9_relat_1(X3,X4),X1),k1_relat_1(k5_relat_1(X3,X2)))
    | ~ r2_hidden(X1,k9_relat_1(X3,X4))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk1_0,esk3_0),k1_zfmisc_1(k1_relat_1(esk2_0)))
    | m1_subset_1(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_55]),c_0_56])).

cnf(c_0_67,plain,
    ( m1_subset_1(esk4_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_35])).

cnf(c_0_68,negated_conjecture,
    ( ~ m1_subset_1(k9_relat_1(esk1_0,esk3_0),k1_zfmisc_1(k1_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk1_0,esk3_0),k1_zfmisc_1(k1_relat_1(esk2_0)))
    | ~ v1_xboole_0(k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( v1_xboole_0(k1_relat_1(k5_relat_1(X1,X2)))
    | r2_hidden(X3,k1_relat_1(X2))
    | ~ m1_subset_1(esk4_4(X1,X4,k9_relat_1(X1,X4),X3),k1_relat_1(k5_relat_1(X1,X2)))
    | ~ r2_hidden(X3,k9_relat_1(X1,X4))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_55])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk4_4(X1,esk3_0,k9_relat_1(X1,esk3_0),X2),k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r2_hidden(X2,k9_relat_1(X1,esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,k9_relat_1(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk7_2(k9_relat_1(esk1_0,esk3_0),X1),k1_relat_1(esk2_0))
    | r1_tarski(k9_relat_1(esk1_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_33])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_62])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_74]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
