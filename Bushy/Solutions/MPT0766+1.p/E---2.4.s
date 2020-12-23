%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t12_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:10 EDT 2019

% Result     : Theorem 0.34s
% Output     : CNFRefutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 284 expanded)
%              Number of clauses        :   40 ( 120 expanded)
%              Number of leaves         :   10 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 (1674 expanded)
%              Number of equality atoms :   19 ( 126 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(s1_xboole_0__e7_18__wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => ? [X3] :
        ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,k3_relat_1(X1))
            & ~ r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t12_wellord1.p',s1_xboole_0__e7_18__wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t12_wellord1.p',d3_tarski)).

fof(t12_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & ? [X3] :
                  ( r2_hidden(X3,k3_relat_1(X1))
                  & ~ r2_hidden(k4_tarski(X3,X2),X1) )
              & ! [X3] :
                  ~ ( r2_hidden(X3,k3_relat_1(X1))
                    & r2_hidden(k4_tarski(X2,X3),X1)
                    & ! [X4] :
                        ~ ( r2_hidden(X4,k3_relat_1(X1))
                          & r2_hidden(k4_tarski(X2,X4),X1)
                          & X4 != X2
                          & ~ r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t12_wellord1.p',t12_wellord1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t12_wellord1.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t12_wellord1.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t12_wellord1.p',t2_subset)).

fof(t10_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t12_wellord1.p',t10_wellord1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t12_wellord1.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t12_wellord1.p',d2_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t12_wellord1.p',t6_boole)).

fof(c_0_10,plain,(
    ! [X34,X35,X37,X38] :
      ( ( r2_hidden(X37,k3_relat_1(X34))
        | ~ r2_hidden(X37,esk11_2(X34,X35))
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(k4_tarski(X37,X35),X34)
        | ~ r2_hidden(X37,esk11_2(X34,X35))
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(X38,k3_relat_1(X34))
        | r2_hidden(k4_tarski(X38,X35),X34)
        | r2_hidden(X38,esk11_2(X34,X35))
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_xboole_0__e7_18__wellord1])])])])])])])).

fof(c_0_11,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( ~ r1_tarski(X14,X15)
        | ~ r2_hidden(X16,X14)
        | r2_hidden(X16,X15) )
      & ( r2_hidden(esk5_2(X17,X18),X17)
        | r1_tarski(X17,X18) )
      & ( ~ r2_hidden(esk5_2(X17,X18),X18)
        | r1_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => ! [X2] :
              ~ ( r2_hidden(X2,k3_relat_1(X1))
                & ? [X3] :
                    ( r2_hidden(X3,k3_relat_1(X1))
                    & ~ r2_hidden(k4_tarski(X3,X2),X1) )
                & ! [X3] :
                    ~ ( r2_hidden(X3,k3_relat_1(X1))
                      & r2_hidden(k4_tarski(X2,X3),X1)
                      & ! [X4] :
                          ~ ( r2_hidden(X4,k3_relat_1(X1))
                            & r2_hidden(k4_tarski(X2,X4),X1)
                            & X4 != X2
                            & ~ r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_wellord1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,esk11_2(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ! [X8] :
      ( v1_relat_1(esk1_0)
      & v2_wellord1(esk1_0)
      & r2_hidden(esk2_0,k3_relat_1(esk1_0))
      & r2_hidden(esk3_0,k3_relat_1(esk1_0))
      & ~ r2_hidden(k4_tarski(esk3_0,esk2_0),esk1_0)
      & ( r2_hidden(esk4_1(X8),k3_relat_1(esk1_0))
        | ~ r2_hidden(X8,k3_relat_1(esk1_0))
        | ~ r2_hidden(k4_tarski(esk2_0,X8),esk1_0) )
      & ( r2_hidden(k4_tarski(esk2_0,esk4_1(X8)),esk1_0)
        | ~ r2_hidden(X8,k3_relat_1(esk1_0))
        | ~ r2_hidden(k4_tarski(esk2_0,X8),esk1_0) )
      & ( esk4_1(X8) != esk2_0
        | ~ r2_hidden(X8,k3_relat_1(esk1_0))
        | ~ r2_hidden(k4_tarski(esk2_0,X8),esk1_0) )
      & ( ~ r2_hidden(k4_tarski(X8,esk4_1(X8)),esk1_0)
        | ~ r2_hidden(X8,k3_relat_1(esk1_0))
        | ~ r2_hidden(k4_tarski(esk2_0,X8),esk1_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_16,plain,(
    ! [X53,X54,X55] :
      ( ~ r2_hidden(X53,X54)
      | ~ m1_subset_1(X54,k1_zfmisc_1(X55))
      | ~ v1_xboole_0(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X21] : m1_subset_1(esk6_1(X21),X21) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_18,plain,(
    ! [X46,X47] :
      ( ~ m1_subset_1(X46,X47)
      | v1_xboole_0(X47)
      | r2_hidden(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_19,plain,
    ( r1_tarski(esk11_2(X1,X2),X3)
    | r2_hidden(esk5_2(esk11_2(X1,X2),X3),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X39,X40,X42] :
      ( ( r2_hidden(esk12_2(X39,X40),X40)
        | ~ r1_tarski(X40,k3_relat_1(X39))
        | X40 = k1_xboole_0
        | ~ v2_wellord1(X39)
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(X42,X40)
        | r2_hidden(k4_tarski(esk12_2(X39,X40),X42),X39)
        | ~ r1_tarski(X40,k3_relat_1(X39))
        | X40 = k1_xboole_0
        | ~ v2_wellord1(X39)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord1])])])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk11_2(esk1_0,X1),X2)
    | r2_hidden(esk5_2(esk11_2(esk1_0,X1),X2),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk6_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk6_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_29,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_30,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_31,plain,
    ( r2_hidden(esk12_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk11_2(esk1_0,X1),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v2_wellord1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk12_2(X3,X2),X1),X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k3_relat_1(X3))
    | ~ v2_wellord1(X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | r2_hidden(X1,esk11_2(X2,X3))
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk2_0,k3_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_37,plain,(
    ! [X56] :
      ( ~ v1_xboole_0(X56)
      | X56 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_38,plain,
    ( v1_xboole_0(esk6_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,esk11_2(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( esk11_2(esk1_0,X1) = k1_xboole_0
    | r2_hidden(esk12_2(esk1_0,esk11_2(esk1_0,X1)),esk11_2(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_20])])).

cnf(c_0_42,negated_conjecture,
    ( esk11_2(esk1_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(esk12_2(esk1_0,esk11_2(esk1_0,X1)),X2),esk1_0)
    | ~ r2_hidden(X2,esk11_2(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_33]),c_0_20])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_0,esk11_2(esk1_0,X1))
    | r2_hidden(k4_tarski(esk2_0,X1),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_20])])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( v1_xboole_0(esk6_1(k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk3_0,k3_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( esk11_2(esk1_0,X1) = k1_xboole_0
    | ~ r2_hidden(k4_tarski(esk12_2(esk1_0,esk11_2(esk1_0,X1)),X1),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_20])])).

cnf(c_0_48,negated_conjecture,
    ( esk11_2(esk1_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(esk12_2(esk1_0,esk11_2(esk1_0,X1)),esk2_0),esk1_0)
    | r2_hidden(k4_tarski(esk2_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( esk6_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk3_0,esk11_2(esk1_0,X1))
    | r2_hidden(k4_tarski(esk3_0,X1),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_46]),c_0_20])])).

cnf(c_0_51,negated_conjecture,
    ( esk11_2(esk1_0,esk2_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk2_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_49]),c_0_39])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_0,esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk4_1(X1)),esk1_0)
    | ~ r2_hidden(X1,k3_relat_1(esk1_0))
    | ~ r2_hidden(k4_tarski(esk2_0,X1),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk4_1(X1)),esk1_0)
    | ~ r2_hidden(X1,k3_relat_1(esk1_0))
    | ~ r2_hidden(k4_tarski(esk2_0,X1),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk4_1(esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_36])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_55]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
