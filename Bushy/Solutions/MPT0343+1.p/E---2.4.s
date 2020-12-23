%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t8_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:27 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 771 expanded)
%              Number of clauses        :   37 ( 300 expanded)
%              Number of leaves         :    3 ( 178 expanded)
%              Depth                    :   17
%              Number of atoms          :  124 (4006 expanded)
%              Number of equality atoms :    9 ( 471 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t8_subset_1.p',t8_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/subset_1__t8_subset_1.p',t7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t8_subset_1.p',d10_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( r2_hidden(X4,X2)
                  <=> r2_hidden(X4,X3) ) )
             => X2 = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_subset_1])).

fof(c_0_4,plain,(
    ! [X18,X19,X20] :
      ( ( m1_subset_1(esk5_3(X18,X19,X20),X18)
        | r1_tarski(X19,X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(X18)) )
      & ( r2_hidden(esk5_3(X18,X19,X20),X19)
        | r1_tarski(X19,X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(X18)) )
      & ( ~ r2_hidden(esk5_3(X18,X19,X20),X20)
        | r1_tarski(X19,X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X8] :
      ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
      & ( ~ r2_hidden(X8,esk2_0)
        | r2_hidden(X8,esk3_0)
        | ~ m1_subset_1(X8,esk1_0) )
      & ( ~ r2_hidden(X8,esk3_0)
        | r2_hidden(X8,esk2_0)
        | ~ m1_subset_1(X8,esk1_0) )
      & esk2_0 != esk3_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | r2_hidden(esk5_3(esk1_0,X1,esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | m1_subset_1(esk5_3(esk1_0,esk3_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    | r2_hidden(esk5_3(esk1_0,esk3_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | r2_hidden(esk5_3(esk1_0,X1,esk3_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    | m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk3_0,esk2_0),esk3_0)
    | ~ r1_tarski(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),esk1_0)
    | ~ r1_tarski(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_17]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | m1_subset_1(esk5_3(esk1_0,esk2_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),esk2_0)
    | r2_hidden(esk5_3(esk1_0,esk3_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),esk2_0)
    | m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_9])).

cnf(c_0_26,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),esk2_0)
    | r2_hidden(esk5_3(esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk3_0,esk2_0),esk3_0)
    | m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),esk1_0)
    | m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    | r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_7]),c_0_9])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk3_0,esk2_0),esk2_0)
    | m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_28]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_30]),c_0_15]),c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    | m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_31]),c_0_7]),c_0_9])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),esk3_0)
    | ~ m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_34]),c_0_15]),c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_37]),c_0_9]),c_0_7])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk3_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_38])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_38])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_39]),c_0_40])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_41]),c_0_7]),c_0_9])])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_42]),c_0_38])]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
