%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:08 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  103 (6399 expanded)
%              Number of clauses        :   69 (2613 expanded)
%              Number of leaves         :   17 (1600 expanded)
%              Depth                    :   19
%              Number of atoms          :  268 (21715 expanded)
%              Number of equality atoms :   39 (1942 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t159_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t11_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(fc2_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2)
        & v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => v1_xboole_0(k5_partfun1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t12_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => r2_hidden(X2,k1_funct_2(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_2)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t159_funct_2])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X59,X60,X61,X62] :
      ( ( v1_funct_1(X62)
        | ~ r2_hidden(X62,k5_partfun1(X59,X60,X61))
        | ~ v1_funct_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( v1_funct_2(X62,X59,X60)
        | ~ r2_hidden(X62,k5_partfun1(X59,X60,X61))
        | ~ v1_funct_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
        | ~ r2_hidden(X62,k5_partfun1(X59,X60,X61))
        | ~ v1_funct_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & ~ r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_funct_2(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_21,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X38,X39,X40] :
      ( ( v4_relat_1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v5_relat_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_33,plain,(
    ! [X27] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X27)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_34,plain,(
    ! [X54,X55,X56] :
      ( ( X55 = k1_xboole_0
        | r2_hidden(X56,k1_funct_2(X54,X55))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X54 != k1_xboole_0
        | r2_hidden(X56,k1_funct_2(X54,X55))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(X1,esk4_0,esk5_0)
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_25])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_25])])).

fof(c_0_39,plain,(
    ! [X21,X22] :
      ( ( k2_zfmisc_1(X21,X22) != k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_40,plain,(
    ! [X33,X34] :
      ( ( ~ v5_relat_1(X34,X33)
        | r1_tarski(k2_relat_1(X34),X33)
        | ~ v1_relat_1(X34) )
      & ( ~ r1_tarski(k2_relat_1(X34),X33)
        | v5_relat_1(X34,X33)
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_41,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0)
    | r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1))
    | r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_36])).

fof(c_0_50,plain,(
    ! [X51,X52,X53] :
      ( v1_xboole_0(X51)
      | ~ v1_xboole_0(X52)
      | ~ v1_funct_1(X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | v1_xboole_0(k5_partfun1(X51,X52,X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( v5_relat_1(k2_zfmisc_1(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_54,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

fof(c_0_55,plain,(
    ! [X23,X24] :
      ( ( ~ r1_tarski(X23,k2_zfmisc_1(X23,X24))
        | X23 = k1_xboole_0 )
      & ( ~ r1_tarski(X23,k2_zfmisc_1(X24,X23))
        | X23 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_56,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

cnf(c_0_57,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_24])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1)
    | r2_hidden(esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1),k1_funct_2(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_funct_2(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_63,plain,(
    ! [X20] : r1_tarski(k1_xboole_0,X20) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X3))
    | ~ v1_xboole_0(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_56]),c_0_57])])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = esk6_0
    | ~ r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_73,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_74,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X2))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_75,plain,
    ( m1_subset_1(k2_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_67])).

cnf(c_0_76,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_65]),c_0_71]),c_0_65]),c_0_72])])).

cnf(c_0_78,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_65]),c_0_76]),c_0_65]),c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_77])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_36])).

cnf(c_0_82,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk4_0,k1_xboole_0,k1_xboole_0),k1_funct_2(esk4_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_71]),c_0_71]),c_0_77])).

cnf(c_0_84,plain,
    ( r1_tarski(k5_partfun1(X1,k1_xboole_0,k1_xboole_0),X2)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1),k2_zfmisc_1(esk4_0,esk5_0))
    | r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_48])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_85])).

cnf(c_0_88,plain,
    ( v1_funct_2(X1,X2,k1_xboole_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,k5_partfun1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_65])).

cnf(c_0_89,negated_conjecture,
    ( esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1) = k2_zfmisc_1(esk4_0,esk5_0)
    | r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_87])).

cnf(c_0_91,plain,
    ( v1_funct_2(esk2_2(k5_partfun1(X1,k1_xboole_0,X2),X3),X1,k1_xboole_0)
    | r1_tarski(k5_partfun1(X1,k1_xboole_0,X2),X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_36])).

cnf(c_0_92,negated_conjecture,
    ( esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) = k1_xboole_0
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_71]),c_0_71]),c_0_65]),c_0_71]),c_0_71]),c_0_65]),c_0_71]),c_0_72])]),c_0_90]),c_0_77]),c_0_90]),c_0_77])).

fof(c_0_93,plain,(
    ! [X57,X58] :
      ( ~ v1_funct_1(X58)
      | ~ v1_funct_2(X58,X57,X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X57,X57)))
      | r2_hidden(X58,k1_funct_2(X57,X57)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_2])])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_90]),c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_80]),c_0_44])])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,k1_funct_2(X2,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_80]),c_0_99]),c_0_44])])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.49/0.66  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.49/0.66  # and selection function PSelectComplexPreferEQ.
% 0.49/0.66  #
% 0.49/0.66  # Preprocessing time       : 0.028 s
% 0.49/0.66  # Presaturation interreduction done
% 0.49/0.66  
% 0.49/0.66  # Proof found!
% 0.49/0.66  # SZS status Theorem
% 0.49/0.66  # SZS output start CNFRefutation
% 0.49/0.66  fof(t159_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_funct_2)).
% 0.49/0.66  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.49/0.66  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 0.49/0.66  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.49/0.66  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.49/0.66  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.49/0.66  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.49/0.66  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.49/0.66  fof(t11_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 0.49/0.66  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.49/0.66  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.49/0.66  fof(fc2_partfun1, axiom, ![X1, X2, X3]:((((~(v1_xboole_0(X1))&v1_xboole_0(X2))&v1_funct_1(X3))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>v1_xboole_0(k5_partfun1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_partfun1)).
% 0.49/0.66  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.49/0.66  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.49/0.66  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.49/0.66  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.49/0.66  fof(t12_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>r2_hidden(X2,k1_funct_2(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_2)).
% 0.49/0.66  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)))), inference(assume_negation,[status(cth)],[t159_funct_2])).
% 0.49/0.66  fof(c_0_18, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.49/0.66  fof(c_0_19, plain, ![X59, X60, X61, X62]:(((v1_funct_1(X62)|~r2_hidden(X62,k5_partfun1(X59,X60,X61))|(~v1_funct_1(X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))&(v1_funct_2(X62,X59,X60)|~r2_hidden(X62,k5_partfun1(X59,X60,X61))|(~v1_funct_1(X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))))&(m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|~r2_hidden(X62,k5_partfun1(X59,X60,X61))|(~v1_funct_1(X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.49/0.66  fof(c_0_20, negated_conjecture, ((v1_funct_1(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&~r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_funct_2(esk4_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.49/0.66  fof(c_0_21, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.49/0.66  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.49/0.66  cnf(c_0_23, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.49/0.66  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.49/0.66  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.49/0.66  fof(c_0_26, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.49/0.66  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.49/0.66  cnf(c_0_28, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.49/0.66  fof(c_0_29, plain, ![X38, X39, X40]:((v4_relat_1(X40,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v5_relat_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.49/0.66  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.49/0.66  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.49/0.66  fof(c_0_32, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.49/0.66  fof(c_0_33, plain, ![X27]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X27)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.49/0.66  fof(c_0_34, plain, ![X54, X55, X56]:((X55=k1_xboole_0|r2_hidden(X56,k1_funct_2(X54,X55))|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X55)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&(X54!=k1_xboole_0|r2_hidden(X56,k1_funct_2(X54,X55))|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X55)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).
% 0.49/0.66  cnf(c_0_35, negated_conjecture, (v1_funct_2(X1,esk4_0,esk5_0)|~r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.49/0.66  cnf(c_0_36, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.49/0.66  cnf(c_0_37, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|~r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_25])])).
% 0.49/0.66  cnf(c_0_38, negated_conjecture, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_25])])).
% 0.49/0.66  fof(c_0_39, plain, ![X21, X22]:((k2_zfmisc_1(X21,X22)!=k1_xboole_0|(X21=k1_xboole_0|X22=k1_xboole_0))&((X21!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0)&(X22!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.49/0.66  fof(c_0_40, plain, ![X33, X34]:((~v5_relat_1(X34,X33)|r1_tarski(k2_relat_1(X34),X33)|~v1_relat_1(X34))&(~r1_tarski(k2_relat_1(X34),X33)|v5_relat_1(X34,X33)|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.49/0.66  cnf(c_0_41, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.49/0.66  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.49/0.66  cnf(c_0_43, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.49/0.66  cnf(c_0_44, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.49/0.66  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.49/0.66  cnf(c_0_46, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_funct_2(X3,X1))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.49/0.66  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0)|r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.49/0.66  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.49/0.66  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1))|r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_38, c_0_36])).
% 0.49/0.66  fof(c_0_50, plain, ![X51, X52, X53]:(v1_xboole_0(X51)|~v1_xboole_0(X52)|~v1_funct_1(X53)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|v1_xboole_0(k5_partfun1(X51,X52,X53))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).
% 0.49/0.66  cnf(c_0_51, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.49/0.66  cnf(c_0_52, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.49/0.66  cnf(c_0_53, plain, (v5_relat_1(k2_zfmisc_1(X1,X2),X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.49/0.66  cnf(c_0_54, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.49/0.66  fof(c_0_55, plain, ![X23, X24]:((~r1_tarski(X23,k2_zfmisc_1(X23,X24))|X23=k1_xboole_0)&(~r1_tarski(X23,k2_zfmisc_1(X24,X23))|X23=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.49/0.66  cnf(c_0_56, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_44])).
% 0.49/0.66  cnf(c_0_57, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.49/0.66  cnf(c_0_58, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.49/0.66  cnf(c_0_59, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_45, c_0_24])).
% 0.49/0.66  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.49/0.66  cnf(c_0_61, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1)|r2_hidden(esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1),k1_funct_2(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])).
% 0.49/0.66  cnf(c_0_62, negated_conjecture, (~r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_funct_2(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.49/0.66  fof(c_0_63, plain, ![X20]:r1_tarski(k1_xboole_0,X20), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.49/0.66  cnf(c_0_64, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,X3))|~v1_xboole_0(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.49/0.66  cnf(c_0_65, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_51])).
% 0.49/0.66  cnf(c_0_66, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.49/0.66  cnf(c_0_67, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.49/0.66  cnf(c_0_68, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.49/0.66  cnf(c_0_69, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_56]), c_0_57])])).
% 0.49/0.66  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=esk6_0|~r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.49/0.66  cnf(c_0_71, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.49/0.66  cnf(c_0_72, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.49/0.66  fof(c_0_73, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.49/0.66  cnf(c_0_74, plain, (v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X2))|v1_xboole_0(X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.49/0.66  cnf(c_0_75, plain, (m1_subset_1(k2_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_30, c_0_67])).
% 0.49/0.66  cnf(c_0_76, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.49/0.66  cnf(c_0_77, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_65]), c_0_71]), c_0_65]), c_0_72])])).
% 0.49/0.66  cnf(c_0_78, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.49/0.66  cnf(c_0_79, plain, (v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k1_xboole_0))|v1_xboole_0(X1)|~v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_65]), c_0_76]), c_0_65]), c_0_76])).
% 0.49/0.66  cnf(c_0_80, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_25, c_0_77])).
% 0.49/0.66  cnf(c_0_81, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_78, c_0_36])).
% 0.49/0.66  cnf(c_0_82, plain, (v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k1_xboole_0))|v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.49/0.66  cnf(c_0_83, negated_conjecture, (~r1_tarski(k5_partfun1(esk4_0,k1_xboole_0,k1_xboole_0),k1_funct_2(esk4_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_71]), c_0_71]), c_0_77])).
% 0.49/0.66  cnf(c_0_84, plain, (r1_tarski(k5_partfun1(X1,k1_xboole_0,k1_xboole_0),X2)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.49/0.66  cnf(c_0_85, negated_conjecture, (v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.49/0.66  cnf(c_0_86, negated_conjecture, (r1_tarski(esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1),k2_zfmisc_1(esk4_0,esk5_0))|r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_45, c_0_48])).
% 0.49/0.66  cnf(c_0_87, negated_conjecture, (r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_81, c_0_85])).
% 0.49/0.66  cnf(c_0_88, plain, (v1_funct_2(X1,X2,k1_xboole_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))|~r2_hidden(X1,k5_partfun1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_23, c_0_65])).
% 0.49/0.66  cnf(c_0_89, negated_conjecture, (esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1)=k2_zfmisc_1(esk4_0,esk5_0)|r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),X1)|~r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),esk2_2(k5_partfun1(esk4_0,esk5_0,esk6_0),X1))), inference(spm,[status(thm)],[c_0_58, c_0_86])).
% 0.49/0.66  cnf(c_0_90, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_87])).
% 0.49/0.66  cnf(c_0_91, plain, (v1_funct_2(esk2_2(k5_partfun1(X1,k1_xboole_0,X2),X3),X1,k1_xboole_0)|r1_tarski(k5_partfun1(X1,k1_xboole_0,X2),X3)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_88, c_0_36])).
% 0.49/0.66  cnf(c_0_92, negated_conjecture, (esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)=k1_xboole_0|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_71]), c_0_71]), c_0_65]), c_0_71]), c_0_71]), c_0_65]), c_0_71]), c_0_72])]), c_0_90]), c_0_77]), c_0_90]), c_0_77])).
% 0.49/0.66  fof(c_0_93, plain, ![X57, X58]:(~v1_funct_1(X58)|~v1_funct_2(X58,X57,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X57,X57)))|r2_hidden(X58,k1_funct_2(X57,X57))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_2])])).
% 0.49/0.66  cnf(c_0_94, negated_conjecture, (~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_90]), c_0_90])).
% 0.49/0.66  cnf(c_0_95, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_80]), c_0_44])])).
% 0.49/0.66  cnf(c_0_96, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.49/0.66  cnf(c_0_97, plain, (r2_hidden(X1,k1_funct_2(X2,X2))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.49/0.66  cnf(c_0_98, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.49/0.66  cnf(c_0_99, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_96])).
% 0.49/0.66  cnf(c_0_100, negated_conjecture, (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_92])).
% 0.49/0.66  cnf(c_0_101, negated_conjecture, (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_80]), c_0_99]), c_0_44])])).
% 0.49/0.66  cnf(c_0_102, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_94]), ['proof']).
% 0.49/0.66  # SZS output end CNFRefutation
% 0.49/0.66  # Proof object total steps             : 103
% 0.49/0.66  # Proof object clause steps            : 69
% 0.49/0.66  # Proof object formula steps           : 34
% 0.49/0.66  # Proof object conjectures             : 31
% 0.49/0.66  # Proof object clause conjectures      : 28
% 0.49/0.66  # Proof object formula conjectures     : 3
% 0.49/0.66  # Proof object initial clauses used    : 25
% 0.49/0.66  # Proof object initial formulas used   : 17
% 0.49/0.66  # Proof object generating inferences   : 35
% 0.49/0.66  # Proof object simplifying inferences  : 57
% 0.49/0.66  # Training examples: 0 positive, 0 negative
% 0.49/0.66  # Parsed axioms                        : 23
% 0.49/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.49/0.66  # Initial clauses                      : 40
% 0.49/0.66  # Removed in clause preprocessing      : 0
% 0.49/0.66  # Initial clauses in saturation        : 40
% 0.49/0.66  # Processed clauses                    : 5026
% 0.49/0.66  # ...of these trivial                  : 189
% 0.49/0.66  # ...subsumed                          : 3657
% 0.49/0.66  # ...remaining for further processing  : 1180
% 0.49/0.66  # Other redundant clauses eliminated   : 7
% 0.49/0.66  # Clauses deleted for lack of memory   : 0
% 0.49/0.66  # Backward-subsumed                    : 27
% 0.49/0.66  # Backward-rewritten                   : 583
% 0.49/0.66  # Generated clauses                    : 18623
% 0.49/0.66  # ...of the previous two non-trivial   : 15289
% 0.49/0.66  # Contextual simplify-reflections      : 25
% 0.49/0.66  # Paramodulations                      : 18592
% 0.49/0.66  # Factorizations                       : 24
% 0.49/0.66  # Equation resolutions                 : 7
% 0.49/0.66  # Propositional unsat checks           : 0
% 0.49/0.66  #    Propositional check models        : 0
% 0.49/0.66  #    Propositional check unsatisfiable : 0
% 0.49/0.66  #    Propositional clauses             : 0
% 0.49/0.66  #    Propositional clauses after purity: 0
% 0.49/0.66  #    Propositional unsat core size     : 0
% 0.49/0.66  #    Propositional preprocessing time  : 0.000
% 0.49/0.66  #    Propositional encoding time       : 0.000
% 0.49/0.66  #    Propositional solver time         : 0.000
% 0.49/0.66  #    Success case prop preproc time    : 0.000
% 0.49/0.66  #    Success case prop encoding time   : 0.000
% 0.49/0.66  #    Success case prop solver time     : 0.000
% 0.49/0.66  # Current number of processed clauses  : 526
% 0.49/0.66  #    Positive orientable unit clauses  : 34
% 0.49/0.66  #    Positive unorientable unit clauses: 0
% 0.49/0.66  #    Negative unit clauses             : 1
% 0.49/0.66  #    Non-unit-clauses                  : 491
% 0.49/0.66  # Current number of unprocessed clauses: 9674
% 0.49/0.66  # ...number of literals in the above   : 31065
% 0.49/0.66  # Current number of archived formulas  : 0
% 0.49/0.66  # Current number of archived clauses   : 649
% 0.49/0.66  # Clause-clause subsumption calls (NU) : 111850
% 0.49/0.66  # Rec. Clause-clause subsumption calls : 71265
% 0.49/0.66  # Non-unit clause-clause subsumptions  : 3705
% 0.49/0.66  # Unit Clause-clause subsumption calls : 2581
% 0.49/0.66  # Rewrite failures with RHS unbound    : 0
% 0.49/0.66  # BW rewrite match attempts            : 195
% 0.49/0.66  # BW rewrite match successes           : 7
% 0.49/0.66  # Condensation attempts                : 0
% 0.49/0.66  # Condensation successes               : 0
% 0.49/0.66  # Termbank termtop insertions          : 272386
% 0.49/0.66  
% 0.49/0.66  # -------------------------------------------------
% 0.49/0.66  # User time                : 0.299 s
% 0.49/0.66  # System time              : 0.014 s
% 0.49/0.66  # Total time               : 0.313 s
% 0.49/0.66  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
