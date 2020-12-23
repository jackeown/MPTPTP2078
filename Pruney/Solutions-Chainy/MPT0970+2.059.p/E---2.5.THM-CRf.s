%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:35 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 (18705 expanded)
%              Number of clauses        :   81 (8050 expanded)
%              Number of leaves         :   13 (4431 expanded)
%              Depth                    :   31
%              Number of atoms          :  305 (76278 expanded)
%              Number of equality atoms :  106 (20052 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t16_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] :
                  ~ ( r2_hidden(X5,X1)
                    & X4 = k1_funct_1(X3,X5) ) )
       => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] :
                    ~ ( r2_hidden(X5,X1)
                      & X4 = k1_funct_1(X3,X5) ) )
         => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t16_funct_2])).

cnf(c_0_16,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ! [X42] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk2_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & ( r2_hidden(esk5_1(X42),esk2_0)
        | ~ r2_hidden(X42,esk3_0) )
      & ( X42 = k1_funct_1(esk4_0,esk5_1(X42))
        | ~ r2_hidden(X42,esk3_0) )
      & k2_relset_1(esk2_0,esk3_0,esk4_0) != esk3_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).

cnf(c_0_19,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k2_relset_1(X33,X34,X35) = k2_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_21,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | v1_relat_1(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_22,plain,(
    ! [X19,X20] : v1_relat_1(k2_zfmisc_1(X19,X20)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_23,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ r2_hidden(X16,X15)
      | r2_hidden(X16,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_24,negated_conjecture,
    ( X1 = k1_funct_1(esk4_0,esk5_1(X1))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

fof(c_0_26,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | m1_subset_1(k2_relset_1(X27,X28,X29),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X24,X25,X26] :
      ( ( r2_hidden(X24,k1_relat_1(X26))
        | ~ r2_hidden(k4_tarski(X24,X25),X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( X25 = k1_funct_1(X26,X24)
        | ~ r2_hidden(k4_tarski(X24,X25),X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X24,k1_relat_1(X26))
        | X25 != k1_funct_1(X26,X24)
        | r2_hidden(k4_tarski(X24,X25),X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_30,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_33,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_1(esk1_2(esk3_0,X1))) = esk1_2(esk3_0,X1)
    | X1 = esk3_0
    | r2_hidden(esk1_2(X1,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_40,plain,(
    ! [X36,X37,X38] :
      ( ( ~ v1_funct_2(X38,X36,X37)
        | X36 = k1_relset_1(X36,X37,X38)
        | X37 = k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( X36 != k1_relset_1(X36,X37,X38)
        | v1_funct_2(X38,X36,X37)
        | X37 = k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( ~ v1_funct_2(X38,X36,X37)
        | X36 = k1_relset_1(X36,X37,X38)
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( X36 != k1_relset_1(X36,X37,X38)
        | v1_funct_2(X38,X36,X37)
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( ~ v1_funct_2(X38,X36,X37)
        | X38 = k1_xboole_0
        | X36 = k1_xboole_0
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( X38 != k1_xboole_0
        | v1_funct_2(X38,X36,X37)
        | X36 = k1_xboole_0
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_41,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_1(esk1_2(esk3_0,X1))) = esk1_2(esk3_0,X1)
    | X1 = esk3_0
    | r2_hidden(esk1_2(X1,esk3_0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_28]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k2_relat_1(esk4_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_45,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X2,X1),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_49,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0)))) = esk1_2(esk3_0,k2_relat_1(esk4_0))
    | r2_hidden(esk1_2(k2_relat_1(esk4_0),esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( X1 = k2_relat_1(esk4_0)
    | r2_hidden(esk1_2(k2_relat_1(esk4_0),X1),esk3_0)
    | r2_hidden(esk1_2(X1,k2_relat_1(esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_28])])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0)))) = esk1_2(esk3_0,k2_relat_1(esk4_0))
    | r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,k2_relat_1(esk4_0)),esk3_0)
    | r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_54]),c_0_44])).

fof(c_0_59,plain,(
    ! [X21,X22,X23] :
      ( ( r2_hidden(X21,k1_relat_1(X23))
        | ~ r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(X22,k2_relat_1(X23))
        | ~ r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0)))) = esk1_2(esk3_0,k2_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_57]),c_0_44]),c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk5_1(X1),esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,k2_relat_1(esk4_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_58]),c_0_44])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))),esk1_2(esk3_0,k2_relat_1(esk4_0))),esk4_0)
    | ~ r2_hidden(esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk4_0))
    | ~ r2_hidden(k4_tarski(X2,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_48])).

cnf(c_0_68,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))),esk1_2(esk3_0,k2_relat_1(esk4_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk3_0,k2_relat_1(esk4_0)),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk4_0),esk3_0),k2_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_70]),c_0_44])).

cnf(c_0_72,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk4_0),esk3_0),X1)
    | ~ m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk4_0),esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_43])).

cnf(c_0_74,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_70]),c_0_44])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_73]),c_0_74])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_76])).

cnf(c_0_81,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_82,negated_conjecture,
    ( k1_relset_1(esk2_0,k1_xboole_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_84,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk4_0) = k1_relat_1(esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk5_1(X1),esk2_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_76])).

cnf(c_0_89,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk5_1(X1),k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k2_relat_1(esk4_0)),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_76]),c_0_76])).

cnf(c_0_92,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),esk4_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk5_1(esk1_2(k1_xboole_0,k2_relat_1(esk4_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_1(esk1_2(k1_xboole_0,k2_relat_1(esk4_0)))) = esk1_2(k1_xboole_0,k2_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_76]),c_0_76])).

cnf(c_0_95,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_1(esk1_2(k1_xboole_0,k2_relat_1(esk4_0))),esk1_2(k1_xboole_0,k2_relat_1(esk4_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(k1_xboole_0,k2_relat_1(esk4_0)),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_96])).

cnf(c_0_98,negated_conjecture,
    ( k2_relat_1(esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_76])).

cnf(c_0_99,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk4_0),k1_xboole_0),k2_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_97]),c_0_98])).

cnf(c_0_100,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk4_0),k1_xboole_0),X1)
    | ~ m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_99])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_76])).

cnf(c_0_102,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk4_0),k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_103,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk4_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_97]),c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_102]),c_0_103])).

cnf(c_0_105,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_104]),c_0_105])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:28:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.21/0.44  # and selection function HSelectMinInfpos.
% 0.21/0.44  #
% 0.21/0.44  # Preprocessing time       : 0.039 s
% 0.21/0.44  # Presaturation interreduction done
% 0.21/0.44  
% 0.21/0.44  # Proof found!
% 0.21/0.44  # SZS status Theorem
% 0.21/0.44  # SZS output start CNFRefutation
% 0.21/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.44  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 0.21/0.44  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.44  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.44  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.44  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.44  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.21/0.44  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.21/0.44  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.44  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.44  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 0.21/0.44  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.21/0.44  fof(c_0_13, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.44  fof(c_0_14, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.44  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.21/0.44  cnf(c_0_16, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.44  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  fof(c_0_18, negated_conjecture, ![X42]:(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((r2_hidden(esk5_1(X42),esk2_0)|~r2_hidden(X42,esk3_0))&(X42=k1_funct_1(esk4_0,esk5_1(X42))|~r2_hidden(X42,esk3_0)))&k2_relset_1(esk2_0,esk3_0,esk4_0)!=esk3_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).
% 0.21/0.44  cnf(c_0_19, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.44  fof(c_0_20, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k2_relset_1(X33,X34,X35)=k2_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.44  fof(c_0_21, plain, ![X17, X18]:(~v1_relat_1(X17)|(~m1_subset_1(X18,k1_zfmisc_1(X17))|v1_relat_1(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.44  fof(c_0_22, plain, ![X19, X20]:v1_relat_1(k2_zfmisc_1(X19,X20)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.44  fof(c_0_23, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|(~r2_hidden(X16,X15)|r2_hidden(X16,X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.44  cnf(c_0_24, negated_conjecture, (X1=k1_funct_1(esk4_0,esk5_1(X1))|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_25, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 0.21/0.44  fof(c_0_26, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|m1_subset_1(k2_relset_1(X27,X28,X29),k1_zfmisc_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.21/0.44  cnf(c_0_27, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.44  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  fof(c_0_29, plain, ![X24, X25, X26]:(((r2_hidden(X24,k1_relat_1(X26))|~r2_hidden(k4_tarski(X24,X25),X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(X25=k1_funct_1(X26,X24)|~r2_hidden(k4_tarski(X24,X25),X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))))&(~r2_hidden(X24,k1_relat_1(X26))|X25!=k1_funct_1(X26,X24)|r2_hidden(k4_tarski(X24,X25),X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.21/0.44  cnf(c_0_30, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.44  cnf(c_0_31, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.44  fof(c_0_32, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k1_relset_1(X30,X31,X32)=k1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.44  cnf(c_0_33, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.44  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk4_0,esk5_1(esk1_2(esk3_0,X1)))=esk1_2(esk3_0,X1)|X1=esk3_0|r2_hidden(esk1_2(X1,esk3_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.44  cnf(c_0_35, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.44  cnf(c_0_36, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.44  cnf(c_0_37, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.44  cnf(c_0_39, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.44  fof(c_0_40, plain, ![X36, X37, X38]:((((~v1_funct_2(X38,X36,X37)|X36=k1_relset_1(X36,X37,X38)|X37=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X36!=k1_relset_1(X36,X37,X38)|v1_funct_2(X38,X36,X37)|X37=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&((~v1_funct_2(X38,X36,X37)|X36=k1_relset_1(X36,X37,X38)|X36!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X36!=k1_relset_1(X36,X37,X38)|v1_funct_2(X38,X36,X37)|X36!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))))&((~v1_funct_2(X38,X36,X37)|X38=k1_xboole_0|X36=k1_xboole_0|X37!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X38!=k1_xboole_0|v1_funct_2(X38,X36,X37)|X36=k1_xboole_0|X37!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.44  cnf(c_0_41, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.44  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk4_0,esk5_1(esk1_2(esk3_0,X1)))=esk1_2(esk3_0,X1)|X1=esk3_0|r2_hidden(esk1_2(X1,esk3_0),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.44  cnf(c_0_43, negated_conjecture, (m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_28]), c_0_36])).
% 0.21/0.44  cnf(c_0_44, negated_conjecture, (k2_relat_1(esk4_0)!=esk3_0), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 0.21/0.44  cnf(c_0_45, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X2,X1),X3)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_33, c_0_25])).
% 0.21/0.44  cnf(c_0_46, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_38])).
% 0.21/0.44  cnf(c_0_47, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_28])).
% 0.21/0.44  cnf(c_0_49, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.44  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_51, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_28])).
% 0.21/0.44  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk4_0,esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))))=esk1_2(esk3_0,k2_relat_1(esk4_0))|r2_hidden(esk1_2(k2_relat_1(esk4_0),esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.21/0.44  cnf(c_0_54, negated_conjecture, (X1=k2_relat_1(esk4_0)|r2_hidden(esk1_2(k2_relat_1(esk4_0),X1),esk3_0)|r2_hidden(esk1_2(X1,k2_relat_1(esk4_0)),X1)), inference(spm,[status(thm)],[c_0_45, c_0_43])).
% 0.21/0.44  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),esk4_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.21/0.44  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_28])])).
% 0.21/0.44  cnf(c_0_57, negated_conjecture, (k1_funct_1(esk4_0,esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))))=esk1_2(esk3_0,k2_relat_1(esk4_0))|r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.44  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_2(esk3_0,k2_relat_1(esk4_0)),esk3_0)|r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_54]), c_0_44])).
% 0.21/0.44  fof(c_0_59, plain, ![X21, X22, X23]:((r2_hidden(X21,k1_relat_1(X23))|~r2_hidden(k4_tarski(X21,X22),X23)|~v1_relat_1(X23))&(r2_hidden(X22,k2_relat_1(X23))|~r2_hidden(k4_tarski(X21,X22),X23)|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.21/0.44  cnf(c_0_60, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),esk4_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.44  cnf(c_0_61, negated_conjecture, (k1_funct_1(esk4_0,esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))))=esk1_2(esk3_0,k2_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_57]), c_0_44]), c_0_24])).
% 0.21/0.44  cnf(c_0_62, negated_conjecture, (r2_hidden(esk5_1(X1),esk2_0)|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_2(esk3_0,k2_relat_1(esk4_0)),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_58]), c_0_44])).
% 0.21/0.44  cnf(c_0_64, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.44  cnf(c_0_65, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(k4_tarski(esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))),esk1_2(esk3_0,k2_relat_1(esk4_0))),esk4_0)|~r2_hidden(esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))),esk2_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.44  cnf(c_0_66, negated_conjecture, (r2_hidden(esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))),esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.44  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk4_0))|~r2_hidden(k4_tarski(X2,X1),esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_48])).
% 0.21/0.44  cnf(c_0_68, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(k4_tarski(esk5_1(esk1_2(esk3_0,k2_relat_1(esk4_0))),esk1_2(esk3_0,k2_relat_1(esk4_0))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.21/0.44  cnf(c_0_69, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_2(esk3_0,k2_relat_1(esk4_0)),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.44  cnf(c_0_70, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(esk3_0,k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_69])).
% 0.21/0.44  cnf(c_0_71, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk4_0),esk3_0),k2_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_70]), c_0_44])).
% 0.21/0.44  cnf(c_0_72, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk4_0),esk3_0),X1)|~m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_71])).
% 0.21/0.44  cnf(c_0_73, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk4_0),esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_72, c_0_43])).
% 0.21/0.44  cnf(c_0_74, negated_conjecture, (esk3_0=k1_xboole_0|~r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_70]), c_0_44])).
% 0.21/0.44  cnf(c_0_75, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.44  cnf(c_0_76, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_73]), c_0_74])).
% 0.21/0.44  cnf(c_0_77, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_75])).
% 0.21/0.44  cnf(c_0_78, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_50, c_0_76])).
% 0.21/0.44  cnf(c_0_79, negated_conjecture, (esk2_0=k1_xboole_0|esk4_0=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.21/0.44  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_28, c_0_76])).
% 0.21/0.44  cnf(c_0_81, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.44  cnf(c_0_82, negated_conjecture, (k1_relset_1(esk2_0,k1_xboole_0,esk4_0)=k1_relat_1(esk4_0)), inference(rw,[status(thm)],[c_0_51, c_0_76])).
% 0.21/0.44  cnf(c_0_83, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.21/0.44  cnf(c_0_84, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_81])).
% 0.21/0.44  cnf(c_0_85, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk4_0)=k1_relat_1(esk4_0)|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.21/0.44  cnf(c_0_86, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_80, c_0_83])).
% 0.21/0.44  cnf(c_0_87, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_78, c_0_83])).
% 0.21/0.44  cnf(c_0_88, negated_conjecture, (r2_hidden(esk5_1(X1),esk2_0)|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_62, c_0_76])).
% 0.21/0.44  cnf(c_0_89, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_87])).
% 0.21/0.44  cnf(c_0_90, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk5_1(X1),k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_88, c_0_83])).
% 0.21/0.44  cnf(c_0_91, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k2_relat_1(esk4_0)),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_76]), c_0_76])).
% 0.21/0.44  cnf(c_0_92, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(k4_tarski(X1,k1_funct_1(esk4_0,X1)),esk4_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_89])).
% 0.21/0.44  cnf(c_0_93, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk5_1(esk1_2(k1_xboole_0,k2_relat_1(esk4_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.21/0.44  cnf(c_0_94, negated_conjecture, (k1_funct_1(esk4_0,esk5_1(esk1_2(k1_xboole_0,k2_relat_1(esk4_0))))=esk1_2(k1_xboole_0,k2_relat_1(esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_76]), c_0_76])).
% 0.21/0.44  cnf(c_0_95, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(k4_tarski(esk5_1(esk1_2(k1_xboole_0,k2_relat_1(esk4_0))),esk1_2(k1_xboole_0,k2_relat_1(esk4_0))),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 0.21/0.44  cnf(c_0_96, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(k1_xboole_0,k2_relat_1(esk4_0)),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_95])).
% 0.21/0.44  cnf(c_0_97, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_xboole_0,k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_96])).
% 0.21/0.44  cnf(c_0_98, negated_conjecture, (k2_relat_1(esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_76])).
% 0.21/0.44  cnf(c_0_99, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk4_0),k1_xboole_0),k2_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_97]), c_0_98])).
% 0.21/0.44  cnf(c_0_100, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk4_0),k1_xboole_0),X1)|~m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_99])).
% 0.21/0.44  cnf(c_0_101, negated_conjecture, (m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_43, c_0_76])).
% 0.21/0.44  cnf(c_0_102, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk4_0),k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.21/0.44  cnf(c_0_103, negated_conjecture, (esk4_0=k1_xboole_0|~r1_tarski(k2_relat_1(esk4_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_97]), c_0_98])).
% 0.21/0.44  cnf(c_0_104, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_102]), c_0_103])).
% 0.21/0.44  cnf(c_0_105, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.44  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_104]), c_0_105])]), ['proof']).
% 0.21/0.44  # SZS output end CNFRefutation
% 0.21/0.44  # Proof object total steps             : 107
% 0.21/0.44  # Proof object clause steps            : 81
% 0.21/0.44  # Proof object formula steps           : 26
% 0.21/0.44  # Proof object conjectures             : 62
% 0.21/0.44  # Proof object clause conjectures      : 59
% 0.21/0.44  # Proof object formula conjectures     : 3
% 0.21/0.44  # Proof object initial clauses used    : 21
% 0.21/0.44  # Proof object initial formulas used   : 13
% 0.21/0.44  # Proof object generating inferences   : 45
% 0.21/0.44  # Proof object simplifying inferences  : 41
% 0.21/0.44  # Training examples: 0 positive, 0 negative
% 0.21/0.44  # Parsed axioms                        : 13
% 0.21/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.44  # Initial clauses                      : 31
% 0.21/0.44  # Removed in clause preprocessing      : 0
% 0.21/0.44  # Initial clauses in saturation        : 31
% 0.21/0.44  # Processed clauses                    : 508
% 0.21/0.44  # ...of these trivial                  : 6
% 0.21/0.44  # ...subsumed                          : 149
% 0.21/0.44  # ...remaining for further processing  : 353
% 0.21/0.44  # Other redundant clauses eliminated   : 10
% 0.21/0.44  # Clauses deleted for lack of memory   : 0
% 0.21/0.44  # Backward-subsumed                    : 27
% 0.21/0.44  # Backward-rewritten                   : 248
% 0.21/0.44  # Generated clauses                    : 957
% 0.21/0.44  # ...of the previous two non-trivial   : 952
% 0.21/0.44  # Contextual simplify-reflections      : 7
% 0.21/0.44  # Paramodulations                      : 920
% 0.21/0.44  # Factorizations                       : 28
% 0.21/0.44  # Equation resolutions                 : 10
% 0.21/0.44  # Propositional unsat checks           : 0
% 0.21/0.44  #    Propositional check models        : 0
% 0.21/0.44  #    Propositional check unsatisfiable : 0
% 0.21/0.44  #    Propositional clauses             : 0
% 0.21/0.44  #    Propositional clauses after purity: 0
% 0.21/0.44  #    Propositional unsat core size     : 0
% 0.21/0.44  #    Propositional preprocessing time  : 0.000
% 0.21/0.44  #    Propositional encoding time       : 0.000
% 0.21/0.44  #    Propositional solver time         : 0.000
% 0.21/0.44  #    Success case prop preproc time    : 0.000
% 0.21/0.44  #    Success case prop encoding time   : 0.000
% 0.21/0.44  #    Success case prop solver time     : 0.000
% 0.21/0.44  # Current number of processed clauses  : 42
% 0.21/0.44  #    Positive orientable unit clauses  : 6
% 0.21/0.44  #    Positive unorientable unit clauses: 0
% 0.21/0.44  #    Negative unit clauses             : 0
% 0.21/0.44  #    Non-unit-clauses                  : 36
% 0.21/0.44  # Current number of unprocessed clauses: 424
% 0.21/0.44  # ...number of literals in the above   : 1489
% 0.21/0.44  # Current number of archived formulas  : 0
% 0.21/0.44  # Current number of archived clauses   : 304
% 0.21/0.44  # Clause-clause subsumption calls (NU) : 6656
% 0.21/0.44  # Rec. Clause-clause subsumption calls : 3382
% 0.21/0.44  # Non-unit clause-clause subsumptions  : 180
% 0.21/0.44  # Unit Clause-clause subsumption calls : 83
% 0.21/0.44  # Rewrite failures with RHS unbound    : 0
% 0.21/0.44  # BW rewrite match attempts            : 12
% 0.21/0.44  # BW rewrite match successes           : 7
% 0.21/0.44  # Condensation attempts                : 0
% 0.21/0.44  # Condensation successes               : 0
% 0.21/0.44  # Termbank termtop insertions          : 22563
% 0.21/0.44  
% 0.21/0.44  # -------------------------------------------------
% 0.21/0.44  # User time                : 0.085 s
% 0.21/0.44  # System time              : 0.008 s
% 0.21/0.44  # Total time               : 0.092 s
% 0.21/0.44  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
