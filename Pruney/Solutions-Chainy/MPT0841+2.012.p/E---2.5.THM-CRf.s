%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 178 expanded)
%              Number of clauses        :   29 (  72 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 990 expanded)
%              Number of equality atoms :   12 (  39 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_relat_1(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_12,negated_conjecture,(
    ! [X51] :
      ( ~ v1_xboole_0(esk6_0)
      & ~ v1_xboole_0(esk7_0)
      & ~ v1_xboole_0(esk8_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0)))
      & m1_subset_1(esk10_0,esk6_0)
      & ( ~ r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))
        | ~ m1_subset_1(X51,esk8_0)
        | ~ r2_hidden(k4_tarski(X51,esk10_0),esk9_0)
        | ~ r2_hidden(X51,esk7_0) )
      & ( m1_subset_1(esk11_0,esk8_0)
        | r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0)) )
      & ( r2_hidden(k4_tarski(esk11_0,esk10_0),esk9_0)
        | r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0)) )
      & ( r2_hidden(esk11_0,esk7_0)
        | r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

fof(c_0_13,plain,(
    ! [X35,X36] : v1_relat_1(k2_zfmisc_1(X35,X36)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_14,plain,(
    ! [X23,X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( r2_hidden(k4_tarski(esk2_4(X23,X24,X25,X26),X26),X23)
        | ~ r2_hidden(X26,X25)
        | X25 != k9_relat_1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk2_4(X23,X24,X25,X26),X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k9_relat_1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X29,X28),X23)
        | ~ r2_hidden(X29,X24)
        | r2_hidden(X28,X25)
        | X25 != k9_relat_1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(esk3_3(X23,X30,X31),X31)
        | ~ r2_hidden(k4_tarski(X33,esk3_3(X23,X30,X31)),X23)
        | ~ r2_hidden(X33,X30)
        | X31 = k9_relat_1(X23,X30)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk4_3(X23,X30,X31),esk3_3(X23,X30,X31)),X23)
        | r2_hidden(esk3_3(X23,X30,X31),X31)
        | X31 = k9_relat_1(X23,X30)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk4_3(X23,X30,X31),X30)
        | r2_hidden(esk3_3(X23,X30,X31),X31)
        | X31 = k9_relat_1(X23,X30)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk10_0),esk9_0)
    | r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))
    | r2_hidden(esk10_0,X1)
    | X1 != k9_relat_1(esk9_0,X2)
    | ~ r2_hidden(esk11_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

fof(c_0_22,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k7_relset_1(X42,X43,X44,X45) = k9_relat_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))
    | r2_hidden(esk10_0,k9_relat_1(esk9_0,X1))
    | ~ r2_hidden(esk11_0,X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk11_0,esk7_0)
    | r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))
    | ~ m1_subset_1(X1,esk8_0)
    | ~ r2_hidden(k4_tarski(X1,esk10_0),esk9_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))
    | r2_hidden(esk10_0,k9_relat_1(esk9_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_29,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(X1,esk8_0)
    | ~ r2_hidden(esk10_0,k9_relat_1(esk9_0,esk7_0))
    | ~ r2_hidden(k4_tarski(X1,esk10_0),esk9_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_16])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk10_0,k9_relat_1(esk9_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_26]),c_0_16])])).

fof(c_0_32,plain,(
    ! [X37,X38,X39,X41] :
      ( ( r2_hidden(esk5_3(X37,X38,X39),k1_relat_1(X39))
        | ~ r2_hidden(X37,k9_relat_1(X39,X38))
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(k4_tarski(esk5_3(X37,X38,X39),X37),X39)
        | ~ r2_hidden(X37,k9_relat_1(X39,X38))
        | ~ v1_relat_1(X39) )
      & ( r2_hidden(esk5_3(X37,X38,X39),X38)
        | ~ r2_hidden(X37,k9_relat_1(X39,X38))
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(X41,k1_relat_1(X39))
        | ~ r2_hidden(k4_tarski(X41,X37),X39)
        | ~ r2_hidden(X41,X38)
        | r2_hidden(X37,k9_relat_1(X39,X38))
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(X1,esk8_0)
    | ~ r2_hidden(k4_tarski(X1,esk10_0),esk9_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | m1_subset_1(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(esk5_3(esk10_0,X1,esk9_0),esk8_0)
    | ~ r2_hidden(esk5_3(esk10_0,X1,esk9_0),esk7_0)
    | ~ r2_hidden(esk10_0,k9_relat_1(esk9_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_20])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_41,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r2_hidden(X13,X15)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( r2_hidden(X14,X16)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X14,X16)
        | r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk8_0,esk6_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk5_3(esk10_0,X1,esk9_0),esk7_0)
    | ~ r2_hidden(esk5_3(esk10_0,X1,esk9_0),esk8_0)
    | ~ r2_hidden(esk10_0,k9_relat_1(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,esk9_0),X1),k2_zfmisc_1(esk8_0,esk6_0))
    | ~ r2_hidden(X1,k9_relat_1(esk9_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_36]),c_0_20])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk5_3(esk10_0,esk7_0,esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_31]),c_0_20])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_3(X1,X2,esk9_0),esk8_0)
    | ~ r2_hidden(X1,k9_relat_1(esk9_0,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:27:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t52_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 0.19/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.38  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 0.19/0.38  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.19/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t52_relset_1])).
% 0.19/0.38  fof(c_0_11, plain, ![X21, X22]:(~v1_relat_1(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_relat_1(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.38  fof(c_0_12, negated_conjecture, ![X51]:(~v1_xboole_0(esk6_0)&(~v1_xboole_0(esk7_0)&(~v1_xboole_0(esk8_0)&(m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0)))&(m1_subset_1(esk10_0,esk6_0)&((~r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))|(~m1_subset_1(X51,esk8_0)|~r2_hidden(k4_tarski(X51,esk10_0),esk9_0)|~r2_hidden(X51,esk7_0)))&(((m1_subset_1(esk11_0,esk8_0)|r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0)))&(r2_hidden(k4_tarski(esk11_0,esk10_0),esk9_0)|r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))))&(r2_hidden(esk11_0,esk7_0)|r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).
% 0.19/0.38  fof(c_0_13, plain, ![X35, X36]:v1_relat_1(k2_zfmisc_1(X35,X36)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.38  fof(c_0_14, plain, ![X23, X24, X25, X26, X28, X29, X30, X31, X33]:((((r2_hidden(k4_tarski(esk2_4(X23,X24,X25,X26),X26),X23)|~r2_hidden(X26,X25)|X25!=k9_relat_1(X23,X24)|~v1_relat_1(X23))&(r2_hidden(esk2_4(X23,X24,X25,X26),X24)|~r2_hidden(X26,X25)|X25!=k9_relat_1(X23,X24)|~v1_relat_1(X23)))&(~r2_hidden(k4_tarski(X29,X28),X23)|~r2_hidden(X29,X24)|r2_hidden(X28,X25)|X25!=k9_relat_1(X23,X24)|~v1_relat_1(X23)))&((~r2_hidden(esk3_3(X23,X30,X31),X31)|(~r2_hidden(k4_tarski(X33,esk3_3(X23,X30,X31)),X23)|~r2_hidden(X33,X30))|X31=k9_relat_1(X23,X30)|~v1_relat_1(X23))&((r2_hidden(k4_tarski(esk4_3(X23,X30,X31),esk3_3(X23,X30,X31)),X23)|r2_hidden(esk3_3(X23,X30,X31),X31)|X31=k9_relat_1(X23,X30)|~v1_relat_1(X23))&(r2_hidden(esk4_3(X23,X30,X31),X30)|r2_hidden(esk3_3(X23,X30,X31),X31)|X31=k9_relat_1(X23,X30)|~v1_relat_1(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.19/0.38  cnf(c_0_15, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_18, plain, (r2_hidden(X2,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X5!=k9_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(k4_tarski(esk11_0,esk10_0),esk9_0)|r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))|r2_hidden(esk10_0,X1)|X1!=k9_relat_1(esk9_0,X2)|~r2_hidden(esk11_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.19/0.38  fof(c_0_22, plain, ![X42, X43, X44, X45]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k7_relset_1(X42,X43,X44,X45)=k9_relat_1(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))|r2_hidden(esk10_0,k9_relat_1(esk9_0,X1))|~r2_hidden(esk11_0,X1)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk11_0,esk7_0)|r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (~r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))|~m1_subset_1(X1,esk8_0)|~r2_hidden(k4_tarski(X1,esk10_0),esk9_0)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_26, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(esk8_0,esk6_0,esk9_0,esk7_0))|r2_hidden(esk10_0,k9_relat_1(esk9_0,esk7_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.38  fof(c_0_28, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  fof(c_0_29, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (~m1_subset_1(X1,esk8_0)|~r2_hidden(esk10_0,k9_relat_1(esk9_0,esk7_0))|~r2_hidden(k4_tarski(X1,esk10_0),esk9_0)|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_16])])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk10_0,k9_relat_1(esk9_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_26]), c_0_16])])).
% 0.19/0.38  fof(c_0_32, plain, ![X37, X38, X39, X41]:((((r2_hidden(esk5_3(X37,X38,X39),k1_relat_1(X39))|~r2_hidden(X37,k9_relat_1(X39,X38))|~v1_relat_1(X39))&(r2_hidden(k4_tarski(esk5_3(X37,X38,X39),X37),X39)|~r2_hidden(X37,k9_relat_1(X39,X38))|~v1_relat_1(X39)))&(r2_hidden(esk5_3(X37,X38,X39),X38)|~r2_hidden(X37,k9_relat_1(X39,X38))|~v1_relat_1(X39)))&(~r2_hidden(X41,k1_relat_1(X39))|~r2_hidden(k4_tarski(X41,X37),X39)|~r2_hidden(X41,X38)|r2_hidden(X37,k9_relat_1(X39,X38))|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.19/0.38  cnf(c_0_33, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (~m1_subset_1(X1,esk8_0)|~r2_hidden(k4_tarski(X1,esk10_0),esk9_0)|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 0.19/0.38  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  fof(c_0_37, plain, ![X17, X18]:(~r2_hidden(X17,X18)|m1_subset_1(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.38  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (~m1_subset_1(esk5_3(esk10_0,X1,esk9_0),esk8_0)|~r2_hidden(esk5_3(esk10_0,X1,esk9_0),esk7_0)|~r2_hidden(esk10_0,k9_relat_1(esk9_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_20])])).
% 0.19/0.38  cnf(c_0_40, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  fof(c_0_41, plain, ![X13, X14, X15, X16]:(((r2_hidden(X13,X15)|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)))&(r2_hidden(X14,X16)|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16))))&(~r2_hidden(X13,X15)|~r2_hidden(X14,X16)|r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk8_0,esk6_0))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_38, c_0_16])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk5_3(esk10_0,X1,esk9_0),esk7_0)|~r2_hidden(esk5_3(esk10_0,X1,esk9_0),esk8_0)|~r2_hidden(esk10_0,k9_relat_1(esk9_0,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.38  cnf(c_0_44, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(X1,X2,esk9_0),X1),k2_zfmisc_1(esk8_0,esk6_0))|~r2_hidden(X1,k9_relat_1(esk9_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_36]), c_0_20])])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (~r2_hidden(esk5_3(esk10_0,esk7_0,esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_31]), c_0_20])])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk5_3(X1,X2,esk9_0),esk8_0)|~r2_hidden(X1,k9_relat_1(esk9_0,X2))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_31])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 50
% 0.19/0.38  # Proof object clause steps            : 29
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 21
% 0.19/0.38  # Proof object clause conjectures      : 18
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 14
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 14
% 0.19/0.38  # Proof object simplifying inferences  : 19
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 31
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 31
% 0.19/0.38  # Processed clauses                    : 117
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 6
% 0.19/0.38  # ...remaining for further processing  : 111
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 11
% 0.19/0.38  # Backward-rewritten                   : 11
% 0.19/0.38  # Generated clauses                    : 158
% 0.19/0.38  # ...of the previous two non-trivial   : 149
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 155
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 3
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
% 0.19/0.38  # Current number of processed clauses  : 58
% 0.19/0.38  #    Positive orientable unit clauses  : 10
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 4
% 0.19/0.38  #    Non-unit-clauses                  : 44
% 0.19/0.38  # Current number of unprocessed clauses: 85
% 0.19/0.38  # ...number of literals in the above   : 359
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 53
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 707
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 444
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 15
% 0.19/0.38  # Unit Clause-clause subsumption calls : 36
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 8
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5456
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.036 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
