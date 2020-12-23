%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:23 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 181 expanded)
%              Number of clauses        :   39 (  77 expanded)
%              Number of leaves         :    7 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  202 ( 949 expanded)
%              Number of equality atoms :   52 ( 218 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t9_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(t8_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(k2_relset_1(X1,X2,X4),X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_7,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_8,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | m1_subset_1(k2_relset_1(X27,X28,X29),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X2,X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_2])).

fof(c_0_10,plain,(
    ! [X32,X33,X34,X35] :
      ( ( v1_funct_1(X35)
        | X33 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X32,X33,X35),X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v1_funct_2(X35,X32,X34)
        | X33 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X32,X33,X35),X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X34)))
        | X33 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X32,X33,X35),X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v1_funct_1(X35)
        | X32 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X32,X33,X35),X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v1_funct_2(X35,X32,X34)
        | X32 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X32,X33,X35),X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X34)))
        | X32 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X32,X33,X35),X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

fof(c_0_16,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_relset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(pm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( X1 = o_0_0_xboole_0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),X4) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk2_0) ),
    inference(pm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,plain,
    ( X1 = o_0_0_xboole_0
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),X4) ),
    inference(pm,[status(thm)],[c_0_11,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(pm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,plain,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(X2,X3,X4)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),X4) ),
    inference(rw,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X1,X2) = o_0_0_xboole_0
    | X1 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_15]),c_0_15])).

cnf(c_0_36,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 != o_0_0_xboole_0
    | ~ v1_funct_2(X1,X2,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3) ),
    inference(rw,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0)) ),
    inference(pm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,X1))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_21]),c_0_18])])).

cnf(c_0_39,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33,c_0_18]),c_0_32]),c_0_21])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(pm,[status(thm)],[c_0_23,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( o_0_0_xboole_0 != esk1_0
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(o_0_0_xboole_0))
    | o_0_0_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_18,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,X1)
    | o_0_0_xboole_0 != esk1_0
    | ~ r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_36,c_0_18]),c_0_32]),c_0_21])])).

cnf(c_0_44,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_37,c_0_38]),c_0_34])])).

cnf(c_0_46,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_39,c_0_40]),c_0_24])])).

cnf(c_0_47,negated_conjecture,
    ( o_0_0_xboole_0 != esk1_0
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(pm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | o_0_0_xboole_0 != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43,c_0_40]),c_0_24])])).

cnf(c_0_49,negated_conjecture,
    ( o_0_0_xboole_0 = esk1_0
    | esk2_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_15]),c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0 ),
    inference(pm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( o_0_0_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:52:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.60/0.78  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.60/0.78  # and selection function NoSelection.
% 0.60/0.78  #
% 0.60/0.78  # Preprocessing time       : 0.028 s
% 0.60/0.78  
% 0.60/0.78  # Proof found!
% 0.60/0.78  # SZS status Theorem
% 0.60/0.78  # SZS output start CNFRefutation
% 0.60/0.78  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.60/0.78  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.60/0.78  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 0.60/0.78  fof(t8_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 0.60/0.78  fof(d2_xboole_0, axiom, k1_xboole_0=o_0_0_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_xboole_0)).
% 0.60/0.78  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.60/0.78  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.60/0.78  fof(c_0_7, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.60/0.78  fof(c_0_8, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|m1_subset_1(k2_relset_1(X27,X28,X29),k1_zfmisc_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.60/0.78  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 0.60/0.78  fof(c_0_10, plain, ![X32, X33, X34, X35]:((((v1_funct_1(X35)|X33=k1_xboole_0|~r1_tarski(k2_relset_1(X32,X33,X35),X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(v1_funct_2(X35,X32,X34)|X33=k1_xboole_0|~r1_tarski(k2_relset_1(X32,X33,X35),X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X34)))|X33=k1_xboole_0|~r1_tarski(k2_relset_1(X32,X33,X35),X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(((v1_funct_1(X35)|X32!=k1_xboole_0|~r1_tarski(k2_relset_1(X32,X33,X35),X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(v1_funct_2(X35,X32,X34)|X32!=k1_xboole_0|~r1_tarski(k2_relset_1(X32,X33,X35),X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X34)))|X32!=k1_xboole_0|~r1_tarski(k2_relset_1(X32,X33,X35),X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).
% 0.60/0.78  cnf(c_0_11, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.60/0.78  cnf(c_0_12, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.60/0.78  fof(c_0_13, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk2_0,esk3_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.60/0.78  cnf(c_0_14, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.78  cnf(c_0_15, plain, (k1_xboole_0=o_0_0_xboole_0), inference(split_conjunct,[status(thm)],[d2_xboole_0])).
% 0.60/0.78  fof(c_0_16, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.60/0.78  cnf(c_0_17, plain, (r1_tarski(k2_relset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(pm,[status(thm)],[c_0_11, c_0_12])).
% 0.60/0.78  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.78  fof(c_0_19, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.60/0.78  cnf(c_0_20, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.78  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.78  cnf(c_0_22, plain, (X1=o_0_0_xboole_0|m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_2(X2,X3,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r1_tarski(k2_relset_1(X3,X1,X2),X4)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.60/0.78  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.60/0.78  cnf(c_0_24, negated_conjecture, (r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk2_0)), inference(pm,[status(thm)],[c_0_17, c_0_18])).
% 0.60/0.78  cnf(c_0_25, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.78  cnf(c_0_26, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.78  cnf(c_0_27, plain, (v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.78  cnf(c_0_28, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])])).
% 0.60/0.78  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.60/0.78  cnf(c_0_30, plain, (X1=o_0_0_xboole_0|r1_tarski(X2,k2_zfmisc_1(X3,X4))|~v1_funct_2(X2,X3,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r1_tarski(k2_relset_1(X3,X1,X2),X4)), inference(pm,[status(thm)],[c_0_11, c_0_22])).
% 0.60/0.78  cnf(c_0_31, negated_conjecture, (r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1)|~r1_tarski(esk2_0,X1)), inference(pm,[status(thm)],[c_0_23, c_0_24])).
% 0.60/0.78  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.78  cnf(c_0_33, plain, (X1=o_0_0_xboole_0|v1_funct_2(X2,X3,X4)|~v1_funct_2(X2,X3,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r1_tarski(k2_relset_1(X3,X1,X2),X4)), inference(rw,[status(thm)],[c_0_25, c_0_15])).
% 0.60/0.78  cnf(c_0_34, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.78  cnf(c_0_35, plain, (k2_zfmisc_1(X1,X2)=o_0_0_xboole_0|X1!=o_0_0_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_15]), c_0_15])).
% 0.60/0.78  cnf(c_0_36, plain, (v1_funct_2(X1,X2,X3)|X2!=o_0_0_xboole_0|~v1_funct_2(X1,X2,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~r1_tarski(k2_relset_1(X2,X4,X1),X3)), inference(rw,[status(thm)],[c_0_27, c_0_15])).
% 0.60/0.78  cnf(c_0_37, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0))), inference(pm,[status(thm)],[c_0_28, c_0_29])).
% 0.60/0.78  cnf(c_0_38, negated_conjecture, (esk2_0=o_0_0_xboole_0|r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,X1))|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_21]), c_0_18])])).
% 0.60/0.78  cnf(c_0_39, negated_conjecture, (esk2_0=o_0_0_xboole_0|v1_funct_2(esk4_0,esk1_0,X1)|~r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33, c_0_18]), c_0_32]), c_0_21])])).
% 0.60/0.78  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(pm,[status(thm)],[c_0_23, c_0_34])).
% 0.60/0.78  cnf(c_0_41, negated_conjecture, (o_0_0_xboole_0!=esk1_0|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(o_0_0_xboole_0))), inference(pm,[status(thm)],[c_0_28, c_0_35])).
% 0.60/0.78  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(o_0_0_xboole_0))|o_0_0_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_18, c_0_35])).
% 0.60/0.78  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,X1)|o_0_0_xboole_0!=esk1_0|~r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_36, c_0_18]), c_0_32]), c_0_21])])).
% 0.60/0.78  cnf(c_0_44, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.78  cnf(c_0_45, negated_conjecture, (esk2_0=o_0_0_xboole_0|~v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_37, c_0_38]), c_0_34])])).
% 0.60/0.78  cnf(c_0_46, negated_conjecture, (esk2_0=o_0_0_xboole_0|v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_39, c_0_40]), c_0_24])])).
% 0.60/0.78  cnf(c_0_47, negated_conjecture, (o_0_0_xboole_0!=esk1_0|~v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(pm,[status(thm)],[c_0_41, c_0_42])).
% 0.60/0.78  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|o_0_0_xboole_0!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43, c_0_40]), c_0_24])])).
% 0.60/0.78  cnf(c_0_49, negated_conjecture, (o_0_0_xboole_0=esk1_0|esk2_0!=o_0_0_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_15]), c_0_15])).
% 0.60/0.78  cnf(c_0_50, negated_conjecture, (esk2_0=o_0_0_xboole_0), inference(pm,[status(thm)],[c_0_45, c_0_46])).
% 0.60/0.78  cnf(c_0_51, negated_conjecture, (o_0_0_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_47, c_0_48])).
% 0.60/0.78  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])]), c_0_51]), ['proof']).
% 0.60/0.78  # SZS output end CNFRefutation
% 0.60/0.78  # Proof object total steps             : 53
% 0.60/0.78  # Proof object clause steps            : 39
% 0.60/0.78  # Proof object formula steps           : 14
% 0.60/0.78  # Proof object conjectures             : 27
% 0.60/0.78  # Proof object clause conjectures      : 24
% 0.60/0.78  # Proof object formula conjectures     : 3
% 0.60/0.78  # Proof object initial clauses used    : 15
% 0.60/0.78  # Proof object initial formulas used   : 7
% 0.60/0.78  # Proof object generating inferences   : 17
% 0.60/0.78  # Proof object simplifying inferences  : 28
% 0.60/0.78  # Training examples: 0 positive, 0 negative
% 0.60/0.78  # Parsed axioms                        : 16
% 0.60/0.78  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.78  # Initial clauses                      : 36
% 0.60/0.78  # Removed in clause preprocessing      : 3
% 0.60/0.78  # Initial clauses in saturation        : 33
% 0.60/0.78  # Processed clauses                    : 4777
% 0.60/0.78  # ...of these trivial                  : 76
% 0.60/0.78  # ...subsumed                          : 3569
% 0.60/0.78  # ...remaining for further processing  : 1132
% 0.60/0.78  # Other redundant clauses eliminated   : 0
% 0.60/0.78  # Clauses deleted for lack of memory   : 0
% 0.60/0.78  # Backward-subsumed                    : 164
% 0.60/0.78  # Backward-rewritten                   : 517
% 0.60/0.78  # Generated clauses                    : 42923
% 0.60/0.78  # ...of the previous two non-trivial   : 36892
% 0.60/0.78  # Contextual simplify-reflections      : 0
% 0.60/0.78  # Paramodulations                      : 42879
% 0.60/0.78  # Factorizations                       : 0
% 0.60/0.78  # Equation resolutions                 : 44
% 0.60/0.78  # Propositional unsat checks           : 0
% 0.60/0.78  #    Propositional check models        : 0
% 0.60/0.78  #    Propositional check unsatisfiable : 0
% 0.60/0.78  #    Propositional clauses             : 0
% 0.60/0.78  #    Propositional clauses after purity: 0
% 0.60/0.78  #    Propositional unsat core size     : 0
% 0.60/0.78  #    Propositional preprocessing time  : 0.000
% 0.60/0.78  #    Propositional encoding time       : 0.000
% 0.60/0.78  #    Propositional solver time         : 0.000
% 0.60/0.78  #    Success case prop preproc time    : 0.000
% 0.60/0.78  #    Success case prop encoding time   : 0.000
% 0.60/0.78  #    Success case prop solver time     : 0.000
% 0.60/0.78  # Current number of processed clauses  : 451
% 0.60/0.78  #    Positive orientable unit clauses  : 46
% 0.60/0.78  #    Positive unorientable unit clauses: 0
% 0.60/0.78  #    Negative unit clauses             : 4
% 0.60/0.78  #    Non-unit-clauses                  : 401
% 0.60/0.78  # Current number of unprocessed clauses: 31560
% 0.60/0.78  # ...number of literals in the above   : 145988
% 0.60/0.78  # Current number of archived formulas  : 0
% 0.60/0.78  # Current number of archived clauses   : 681
% 0.60/0.78  # Clause-clause subsumption calls (NU) : 201871
% 0.60/0.78  # Rec. Clause-clause subsumption calls : 144640
% 0.60/0.78  # Non-unit clause-clause subsumptions  : 3089
% 0.60/0.78  # Unit Clause-clause subsumption calls : 1455
% 0.60/0.78  # Rewrite failures with RHS unbound    : 0
% 0.60/0.78  # BW rewrite match attempts            : 37
% 0.60/0.78  # BW rewrite match successes           : 13
% 0.60/0.78  # Condensation attempts                : 0
% 0.60/0.78  # Condensation successes               : 0
% 0.60/0.78  # Termbank termtop insertions          : 244190
% 0.60/0.79  
% 0.60/0.79  # -------------------------------------------------
% 0.60/0.79  # User time                : 0.433 s
% 0.60/0.79  # System time              : 0.023 s
% 0.60/0.79  # Total time               : 0.455 s
% 0.60/0.79  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
