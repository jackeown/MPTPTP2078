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
% DateTime   : Thu Dec  3 10:58:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 693 expanded)
%              Number of clauses        :   63 ( 288 expanded)
%              Number of leaves         :   14 ( 170 expanded)
%              Depth                    :   15
%              Number of atoms          :  269 (3467 expanded)
%              Number of equality atoms :   52 ( 198 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                      <=> ? [X6] :
                            ( m1_subset_1(X6,X3)
                            & r2_hidden(k4_tarski(X6,X5),X4)
                            & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,X3)
                              & r2_hidden(k4_tarski(X6,X5),X4)
                              & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relset_1])).

fof(c_0_15,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k7_relset_1(X42,X43,X44,X45) = k9_relat_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_16,negated_conjecture,(
    ! [X51] :
      ( ~ v1_xboole_0(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))
      & m1_subset_1(esk8_0,esk4_0)
      & ( ~ r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0))
        | ~ m1_subset_1(X51,esk6_0)
        | ~ r2_hidden(k4_tarski(X51,esk8_0),esk7_0)
        | ~ r2_hidden(X51,esk5_0) )
      & ( m1_subset_1(esk9_0,esk6_0)
        | r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0)) )
      & ( r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)
        | r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0)) )
      & ( r2_hidden(esk9_0,esk5_0)
        | r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).

fof(c_0_17,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_18,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | v1_relat_1(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_21,plain,(
    ! [X28,X29] : v1_relat_1(k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_22,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X30,X31,X32,X34] :
      ( ( r2_hidden(esk3_3(X30,X31,X32),k1_relat_1(X32))
        | ~ r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(k4_tarski(esk3_3(X30,X31,X32),X30),X32)
        | ~ r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(esk3_3(X30,X31,X32),X31)
        | ~ r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) )
      & ( ~ r2_hidden(X34,k1_relat_1(X32))
        | ~ r2_hidden(k4_tarski(X34,X30),X32)
        | ~ r2_hidden(X34,X31)
        | r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)
    | r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k7_relset_1(esk6_0,esk4_0,esk7_0,X1) = k9_relat_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(X37,k1_relat_1(X39))
        | ~ r2_hidden(k4_tarski(X37,X38),X39)
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(X38,k2_relat_1(X39))
        | ~ r2_hidden(k4_tarski(X37,X38),X39)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

fof(c_0_30,plain,(
    ! [X35,X36] :
      ( ( k1_relat_1(k2_zfmisc_1(X35,X36)) = X35
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X35,X36)) = X36
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)
    | r2_hidden(esk8_0,k9_relat_1(esk7_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_19]),c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk9_0,esk5_0)
    | r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk6_0,esk4_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),esk7_0)
    | r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0))
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,esk8_0),esk7_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk8_0,k9_relat_1(esk7_0,esk5_0))
    | r2_hidden(esk9_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_26])).

fof(c_0_44,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | m1_subset_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(X3,X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_28])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),k2_zfmisc_1(esk6_0,esk4_0))
    | r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,esk8_0),esk7_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk5_0)
    | r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_35])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),esk7_0)
    | r2_hidden(esk9_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_43]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk9_0,esk6_0)
    | r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0)
    | r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)
    | ~ m1_subset_1(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_40]),c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),k2_zfmisc_1(esk6_0,esk4_0))
    | r2_hidden(esk9_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk9_0,esk5_0)
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,esk8_0),esk7_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk5_0)
    | r2_hidden(esk9_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk9_0,esk6_0)
    | r2_hidden(esk8_0,k9_relat_1(esk7_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_51,c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0)
    | r2_hidden(esk9_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk9_0,esk5_0)
    | ~ m1_subset_1(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_49]),c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk9_0,esk6_0)
    | r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_58]),c_0_35])])).

fof(c_0_64,plain,(
    ! [X18,X19] :
      ( ~ r2_hidden(X18,X19)
      | k2_xboole_0(k1_tarski(X18),X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

fof(c_0_65,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk8_0,k9_relat_1(esk7_0,X1))
    | ~ r2_hidden(esk9_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_35])])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(esk9_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_61]),c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk9_0,esk6_0)
    | r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),k2_zfmisc_1(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk9_0,esk6_0)
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,esk8_0),esk7_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_50])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk9_0,esk6_0)
    | r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_58]),c_0_35])])).

fof(c_0_71,plain,(
    ! [X20,X21] : k2_xboole_0(k1_tarski(X20),X21) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_72,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_74,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_75,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(esk8_0,k9_relat_1(esk7_0,esk5_0))
    | ~ r2_hidden(k4_tarski(X1,esk8_0),esk7_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_26])).

cnf(c_0_76,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(esk8_0,k9_relat_1(esk7_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | m1_subset_1(esk9_0,esk6_0)
    | r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk9_0,esk6_0)
    | ~ m1_subset_1(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_63]),c_0_70])).

cnf(c_0_79,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,esk8_0),esk7_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | m1_subset_1(esk9_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_77]),c_0_78])).

cnf(c_0_84,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_79,c_0_73])).

cnf(c_0_85,plain,
    ( k2_xboole_0(k2_tarski(esk1_1(X1),esk1_1(X1)),X1) = X1
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_87,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_60]),c_0_67]),c_0_83])).

cnf(c_0_88,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.19/0.44  # and selection function PSelectComplexPreferEQ.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.040 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t52_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 0.19/0.44  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.44  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.44  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.44  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.19/0.44  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.19/0.44  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 0.19/0.44  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.44  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.19/0.44  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.44  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.44  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.44  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t52_relset_1])).
% 0.19/0.44  fof(c_0_15, plain, ![X42, X43, X44, X45]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k7_relset_1(X42,X43,X44,X45)=k9_relat_1(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.44  fof(c_0_16, negated_conjecture, ![X51]:(~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))&(m1_subset_1(esk8_0,esk4_0)&((~r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0))|(~m1_subset_1(X51,esk6_0)|~r2_hidden(k4_tarski(X51,esk8_0),esk7_0)|~r2_hidden(X51,esk5_0)))&(((m1_subset_1(esk9_0,esk6_0)|r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0)))&(r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0))))&(r2_hidden(esk9_0,esk5_0)|r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).
% 0.19/0.44  fof(c_0_17, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.44  cnf(c_0_18, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  fof(c_0_20, plain, ![X26, X27]:(~v1_relat_1(X26)|(~m1_subset_1(X27,k1_zfmisc_1(X26))|v1_relat_1(X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.44  fof(c_0_21, plain, ![X28, X29]:v1_relat_1(k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.44  fof(c_0_22, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.44  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  fof(c_0_24, plain, ![X30, X31, X32, X34]:((((r2_hidden(esk3_3(X30,X31,X32),k1_relat_1(X32))|~r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32))&(r2_hidden(k4_tarski(esk3_3(X30,X31,X32),X30),X32)|~r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32)))&(r2_hidden(esk3_3(X30,X31,X32),X31)|~r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32)))&(~r2_hidden(X34,k1_relat_1(X32))|~r2_hidden(k4_tarski(X34,X30),X32)|~r2_hidden(X34,X31)|r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.19/0.44  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_26, negated_conjecture, (k7_relset_1(esk6_0,esk4_0,esk7_0,X1)=k9_relat_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.44  cnf(c_0_27, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_28, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  fof(c_0_29, plain, ![X37, X38, X39]:((r2_hidden(X37,k1_relat_1(X39))|~r2_hidden(k4_tarski(X37,X38),X39)|~v1_relat_1(X39))&(r2_hidden(X38,k2_relat_1(X39))|~r2_hidden(k4_tarski(X37,X38),X39)|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.19/0.44  fof(c_0_30, plain, ![X35, X36]:((k1_relat_1(k2_zfmisc_1(X35,X36))=X35|(X35=k1_xboole_0|X36=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X35,X36))=X36|(X35=k1_xboole_0|X36=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.19/0.44  cnf(c_0_31, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  cnf(c_0_32, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.19/0.44  cnf(c_0_33, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)|r2_hidden(esk8_0,k9_relat_1(esk7_0,esk5_0))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.44  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_19]), c_0_28])])).
% 0.19/0.44  cnf(c_0_36, negated_conjecture, (r2_hidden(esk9_0,esk5_0)|r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_37, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  cnf(c_0_38, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk6_0,esk4_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.44  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),esk7_0)|r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.19/0.44  cnf(c_0_41, negated_conjecture, (~r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0))|~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(X1,esk8_0),esk7_0)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_42, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_43, negated_conjecture, (r2_hidden(esk8_0,k9_relat_1(esk7_0,esk5_0))|r2_hidden(esk9_0,esk5_0)), inference(rw,[status(thm)],[c_0_36, c_0_26])).
% 0.19/0.44  fof(c_0_44, plain, ![X22, X23]:(~r2_hidden(X22,X23)|m1_subset_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.44  cnf(c_0_45, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r2_hidden(X3,X1)|~r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_28])])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),k2_zfmisc_1(esk6_0,esk4_0))|r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.44  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)|~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(X1,esk8_0),esk7_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_25])).
% 0.19/0.44  cnf(c_0_48, negated_conjecture, (r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk5_0)|r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_34]), c_0_35])])).
% 0.19/0.44  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),esk7_0)|r2_hidden(esk9_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_43]), c_0_35])])).
% 0.19/0.44  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk9_0,esk6_0)|r2_hidden(esk8_0,k7_relset_1(esk6_0,esk4_0,esk7_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_51, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_52, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (esk4_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0)|r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.44  cnf(c_0_54, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)|~m1_subset_1(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_40]), c_0_48])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),k2_zfmisc_1(esk6_0,esk4_0))|r2_hidden(esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_49])).
% 0.19/0.44  cnf(c_0_56, negated_conjecture, (r2_hidden(esk9_0,esk5_0)|~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(X1,esk8_0),esk7_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 0.19/0.44  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk5_0)|r2_hidden(esk9_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35])])).
% 0.19/0.44  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk9_0,esk6_0)|r2_hidden(esk8_0,k9_relat_1(esk7_0,esk5_0))), inference(rw,[status(thm)],[c_0_50, c_0_26])).
% 0.19/0.44  cnf(c_0_59, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_51, c_0_37])).
% 0.19/0.44  cnf(c_0_60, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (esk4_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0)|r2_hidden(esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_55])).
% 0.19/0.44  cnf(c_0_62, negated_conjecture, (r2_hidden(esk9_0,esk5_0)|~m1_subset_1(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_49]), c_0_57])).
% 0.19/0.44  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk9_0,esk6_0)|r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_58]), c_0_35])])).
% 0.19/0.44  fof(c_0_64, plain, ![X18, X19]:(~r2_hidden(X18,X19)|k2_xboole_0(k1_tarski(X18),X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.19/0.44  fof(c_0_65, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (esk4_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(esk8_0,k9_relat_1(esk7_0,X1))|~r2_hidden(esk9_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_35])])).
% 0.19/0.44  cnf(c_0_67, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(esk9_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_61]), c_0_62])).
% 0.19/0.44  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk9_0,esk6_0)|r2_hidden(k4_tarski(esk3_3(esk8_0,esk5_0,esk7_0),esk8_0),k2_zfmisc_1(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_63])).
% 0.19/0.44  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk9_0,esk6_0)|~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(X1,esk8_0),esk7_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_50])).
% 0.19/0.44  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk9_0,esk6_0)|r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_58]), c_0_35])])).
% 0.19/0.44  fof(c_0_71, plain, ![X20, X21]:k2_xboole_0(k1_tarski(X20),X21)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.19/0.44  cnf(c_0_72, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.44  cnf(c_0_73, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.44  fof(c_0_74, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.44  cnf(c_0_75, negated_conjecture, (~m1_subset_1(X1,esk6_0)|~r2_hidden(esk8_0,k9_relat_1(esk7_0,esk5_0))|~r2_hidden(k4_tarski(X1,esk8_0),esk7_0)|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[c_0_41, c_0_26])).
% 0.19/0.44  cnf(c_0_76, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(esk8_0,k9_relat_1(esk7_0,esk5_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.44  cnf(c_0_77, negated_conjecture, (esk4_0=k1_xboole_0|esk6_0=k1_xboole_0|m1_subset_1(esk9_0,esk6_0)|r2_hidden(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_68])).
% 0.19/0.44  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk9_0,esk6_0)|~m1_subset_1(esk3_3(esk8_0,esk5_0,esk7_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_63]), c_0_70])).
% 0.19/0.44  cnf(c_0_79, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.44  cnf(c_0_80, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.44  cnf(c_0_81, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (esk4_0=k1_xboole_0|esk6_0=k1_xboole_0|~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(X1,esk8_0),esk7_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.44  cnf(c_0_83, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0|m1_subset_1(esk9_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_77]), c_0_78])).
% 0.19/0.44  cnf(c_0_84, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_79, c_0_73])).
% 0.19/0.44  cnf(c_0_85, plain, (k2_xboole_0(k2_tarski(esk1_1(X1),esk1_1(X1)),X1)=X1|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.44  cnf(c_0_86, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_87, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_60]), c_0_67]), c_0_83])).
% 0.19/0.44  cnf(c_0_88, plain, (v1_xboole_0(k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85])])).
% 0.19/0.44  cnf(c_0_89, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 0.19/0.44  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90]), c_0_88])]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 92
% 0.19/0.44  # Proof object clause steps            : 63
% 0.19/0.44  # Proof object formula steps           : 29
% 0.19/0.44  # Proof object conjectures             : 45
% 0.19/0.44  # Proof object clause conjectures      : 42
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 22
% 0.19/0.44  # Proof object initial formulas used   : 14
% 0.19/0.44  # Proof object generating inferences   : 33
% 0.19/0.44  # Proof object simplifying inferences  : 39
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 15
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 33
% 0.19/0.44  # Removed in clause preprocessing      : 1
% 0.19/0.44  # Initial clauses in saturation        : 32
% 0.19/0.44  # Processed clauses                    : 387
% 0.19/0.44  # ...of these trivial                  : 2
% 0.19/0.44  # ...subsumed                          : 70
% 0.19/0.44  # ...remaining for further processing  : 315
% 0.19/0.44  # Other redundant clauses eliminated   : 10
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 53
% 0.19/0.44  # Backward-rewritten                   : 72
% 0.19/0.44  # Generated clauses                    : 1137
% 0.19/0.44  # ...of the previous two non-trivial   : 1079
% 0.19/0.44  # Contextual simplify-reflections      : 11
% 0.19/0.44  # Paramodulations                      : 1108
% 0.19/0.44  # Factorizations                       : 16
% 0.19/0.44  # Equation resolutions                 : 10
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 155
% 0.19/0.44  #    Positive orientable unit clauses  : 25
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 4
% 0.19/0.44  #    Non-unit-clauses                  : 126
% 0.19/0.44  # Current number of unprocessed clauses: 609
% 0.19/0.44  # ...number of literals in the above   : 2259
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 161
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 3941
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 2230
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 107
% 0.19/0.44  # Unit Clause-clause subsumption calls : 284
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 22
% 0.19/0.44  # BW rewrite match successes           : 5
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 15818
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.091 s
% 0.19/0.44  # System time              : 0.008 s
% 0.19/0.44  # Total time               : 0.099 s
% 0.19/0.44  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
