%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:04 EST 2020

% Result     : Theorem 8.10s
% Output     : CNFRefutation 8.10s
% Verified   : 
% Statistics : Number of formulae       :  115 (1389 expanded)
%              Number of clauses        :   92 ( 644 expanded)
%              Number of leaves         :   11 ( 334 expanded)
%              Depth                    :   22
%              Number of atoms          :  361 (6225 expanded)
%              Number of equality atoms :   92 (1830 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t18_funct_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(k2_relat_1(X2),X1)
         => ( v1_funct_1(X2)
            & v1_funct_2(X2,k1_relat_1(X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_funct_2])).

fof(c_0_12,plain,(
    ! [X15,X16,X17,X19,X20,X21,X23] :
      ( ( r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X15))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X17 = k1_funct_1(X15,esk2_3(X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(X20,k1_relat_1(X15))
        | X19 != k1_funct_1(X15,X20)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(esk3_2(X15,X21),X21)
        | ~ r2_hidden(X23,k1_relat_1(X15))
        | esk3_2(X15,X21) != k1_funct_1(X15,X23)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk4_2(X15,X21),k1_relat_1(X15))
        | r2_hidden(esk3_2(X15,X21),X21)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk3_2(X15,X21) = k1_funct_1(X15,esk4_2(X15,X21))
        | r2_hidden(esk3_2(X15,X21),X21)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_13,plain,(
    ! [X25,X26] :
      ( ( v1_relat_1(esk5_2(X25,X26))
        | X25 = k1_xboole_0 )
      & ( v1_funct_1(esk5_2(X25,X26))
        | X25 = k1_xboole_0 )
      & ( X26 = k1_relat_1(esk5_2(X25,X26))
        | X25 = k1_xboole_0 )
      & ( r1_tarski(k2_relat_1(esk5_2(X25,X26)),X25)
        | X25 = k1_xboole_0 )
      & ( v1_relat_1(esk5_2(X25,X26))
        | X26 != k1_xboole_0 )
      & ( v1_funct_1(esk5_2(X25,X26))
        | X26 != k1_xboole_0 )
      & ( X26 = k1_relat_1(esk5_2(X25,X26))
        | X26 != k1_xboole_0 )
      & ( r1_tarski(k2_relat_1(esk5_2(X25,X26)),X25)
        | X26 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_1])])])])).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ r1_tarski(k1_relat_1(X35),X33)
      | ~ r1_tarski(k2_relat_1(X35),X34)
      | m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & r1_tarski(k2_relat_1(esk7_0),esk6_0)
    & ( ~ v1_funct_1(esk7_0)
      | ~ v1_funct_2(esk7_0,k1_relat_1(esk7_0),esk6_0)
      | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k1_relat_1(esk5_2(X2,X1))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_funct_1(esk5_2(X1,X2))
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_relat_1(esk5_2(X1,X2))
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_23,plain,(
    ! [X14] :
      ( ~ r1_tarski(X14,k1_xboole_0)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_24,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_funct_1(esk7_0)
    | ~ v1_funct_2(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_29,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | ~ r1_tarski(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_31,plain,
    ( k1_relat_1(esk5_2(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( v1_funct_1(esk5_2(X1,k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( v1_relat_1(esk5_2(X1,k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_relat_1(esk5_2(X1,X2)),X1)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X1)
    | ~ r1_tarski(k1_relat_1(X2),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_40,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,k1_relat_1(esk7_0),esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( r2_hidden(k1_funct_1(esk5_2(X1,k1_xboole_0),X2),k2_relat_1(esk5_2(X1,k1_xboole_0)))
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_relat_1(esk5_2(X1,k1_xboole_0)),X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v1_funct_2(esk7_0,X1,esk6_0)
    | k1_relset_1(X1,esk6_0,esk7_0) != X1
    | ~ r1_tarski(k1_relat_1(esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_48,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,k1_relat_1(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_25]),c_0_39]),c_0_38]),c_0_42])])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_35])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk5_2(X2,k1_xboole_0)),k1_funct_1(esk5_2(X2,k1_xboole_0),X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_relat_1(esk5_2(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48])]),c_0_42])]),c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),k1_xboole_0)
    | ~ r1_tarski(X1,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_50])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_relat_1(esk5_2(X1,X2)),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_59,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),k1_xboole_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),X2)
    | ~ r1_tarski(X1,k2_relat_1(esk7_0))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_34])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_50])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_relat_1(esk5_2(X1,X2)),X1)
    | r1_tarski(k2_relat_1(esk5_2(X3,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_56])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_55]),c_0_34])])).

cnf(c_0_65,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_25]),c_0_39]),c_0_38]),c_0_42])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r1_tarski(X1,k2_relat_1(esk7_0))
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_relat_1(esk5_2(X1,X1)),X1) ),
    inference(ef,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_55]),c_0_34])])).

cnf(c_0_71,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),esk1_2(k2_relat_1(X1),X2)),k1_relat_1(X1))
    | r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_35]),c_0_57])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))),esk6_0)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X2,X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_55]),c_0_34])])).

cnf(c_0_76,plain,
    ( r1_tarski(k2_relat_1(esk5_2(X1,k1_xboole_0)),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_32]),c_0_31]),c_0_33])]),c_0_57])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_27]),c_0_39])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))),esk6_0)
    | ~ r1_tarski(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_34])).

cnf(c_0_79,plain,
    ( v1_funct_1(esk5_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_80,plain,
    ( v1_relat_1(esk5_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X3,k2_relat_1(esk5_2(X4,k1_xboole_0)))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_66])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))),k1_xboole_0)
    | ~ r1_tarski(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_35]),c_0_34])])).

cnf(c_0_84,plain,
    ( v1_funct_1(esk5_2(X1,X2))
    | v1_funct_1(esk5_2(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_79])).

cnf(c_0_85,plain,
    ( v1_relat_1(esk5_2(X1,X2))
    | v1_relat_1(esk5_2(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))),X1)
    | ~ r1_tarski(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_83])).

cnf(c_0_88,plain,
    ( v1_funct_1(esk5_2(X1,X1)) ),
    inference(ef,[status(thm)],[c_0_84])).

cnf(c_0_89,plain,
    ( v1_relat_1(esk5_2(X1,X1)) ),
    inference(ef,[status(thm)],[c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk5_2(k1_relat_1(esk7_0),k1_relat_1(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_69])).

cnf(c_0_91,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))))
    | ~ r1_tarski(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_87]),c_0_88]),c_0_89])])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_2(k1_relat_1(esk7_0),k1_relat_1(esk7_0))),X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_66])).

cnf(c_0_93,negated_conjecture,
    ( ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0)))
    | ~ r2_hidden(X1,k1_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_53]),c_0_34])])).

cnf(c_0_94,plain,
    ( X1 = k1_relat_1(esk5_2(X2,X1))
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk5_2(k1_relat_1(esk7_0),k1_relat_1(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_92]),c_0_88]),c_0_89])])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_25]),c_0_39]),c_0_73]),c_0_42])])).

cnf(c_0_97,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | X2 = X3
    | ~ r1_tarski(k1_relat_1(esk5_2(X1,X3)),X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_50])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_2(k1_relat_1(esk7_0),k1_relat_1(esk7_0))),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_66])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))),X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_66])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,k1_xboole_0,esk6_0)
    | ~ r1_tarski(k1_relat_1(esk7_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_35])).

cnf(c_0_102,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_xboole_0
    | X1 = k1_relat_1(esk7_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | X1 = k2_relat_1(esk7_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,X1,esk6_0)
    | ~ r1_tarski(k1_relat_1(esk7_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_55]),c_0_34])])).

cnf(c_0_106,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_102,c_0_25])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_34])).

cnf(c_0_108,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_104,c_0_34])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,X1,esk6_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_82])])).

cnf(c_0_110,negated_conjecture,
    ( v1_funct_2(esk7_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,esk7_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_39]),c_0_34]),c_0_108]),c_0_34])])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,esk6_0)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,esk7_0)
    | ~ r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_55])).

cnf(c_0_112,negated_conjecture,
    ( v1_funct_2(esk7_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_48]),c_0_107])])).

cnf(c_0_113,negated_conjecture,
    ( ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_34]),c_0_42])])).

cnf(c_0_114,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_25]),c_0_39]),c_0_73]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 8.10/8.30  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 8.10/8.30  # and selection function PSelectUnlessUniqMaxPos.
% 8.10/8.30  #
% 8.10/8.30  # Preprocessing time       : 0.028 s
% 8.10/8.30  # Presaturation interreduction done
% 8.10/8.30  
% 8.10/8.30  # Proof found!
% 8.10/8.30  # SZS status Theorem
% 8.10/8.30  # SZS output start CNFRefutation
% 8.10/8.30  fof(t4_funct_2, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 8.10/8.30  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 8.10/8.30  fof(t18_funct_1, axiom, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 8.10/8.30  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.10/8.30  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 8.10/8.30  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.10/8.30  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.10/8.30  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.10/8.30  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.10/8.30  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.10/8.30  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.10/8.30  fof(c_0_11, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))))), inference(assume_negation,[status(cth)],[t4_funct_2])).
% 8.10/8.30  fof(c_0_12, plain, ![X15, X16, X17, X19, X20, X21, X23]:((((r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X15))|~r2_hidden(X17,X16)|X16!=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(X17=k1_funct_1(X15,esk2_3(X15,X16,X17))|~r2_hidden(X17,X16)|X16!=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&(~r2_hidden(X20,k1_relat_1(X15))|X19!=k1_funct_1(X15,X20)|r2_hidden(X19,X16)|X16!=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&((~r2_hidden(esk3_2(X15,X21),X21)|(~r2_hidden(X23,k1_relat_1(X15))|esk3_2(X15,X21)!=k1_funct_1(X15,X23))|X21=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&((r2_hidden(esk4_2(X15,X21),k1_relat_1(X15))|r2_hidden(esk3_2(X15,X21),X21)|X21=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(esk3_2(X15,X21)=k1_funct_1(X15,esk4_2(X15,X21))|r2_hidden(esk3_2(X15,X21),X21)|X21=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 8.10/8.30  fof(c_0_13, plain, ![X25, X26]:((((v1_relat_1(esk5_2(X25,X26))|X25=k1_xboole_0)&(v1_funct_1(esk5_2(X25,X26))|X25=k1_xboole_0))&((X26=k1_relat_1(esk5_2(X25,X26))|X25=k1_xboole_0)&(r1_tarski(k2_relat_1(esk5_2(X25,X26)),X25)|X25=k1_xboole_0)))&(((v1_relat_1(esk5_2(X25,X26))|X26!=k1_xboole_0)&(v1_funct_1(esk5_2(X25,X26))|X26!=k1_xboole_0))&((X26=k1_relat_1(esk5_2(X25,X26))|X26!=k1_xboole_0)&(r1_tarski(k2_relat_1(esk5_2(X25,X26)),X25)|X26!=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_1])])])])).
% 8.10/8.30  fof(c_0_14, plain, ![X36, X37, X38]:((((~v1_funct_2(X38,X36,X37)|X36=k1_relset_1(X36,X37,X38)|X37=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X36!=k1_relset_1(X36,X37,X38)|v1_funct_2(X38,X36,X37)|X37=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&((~v1_funct_2(X38,X36,X37)|X36=k1_relset_1(X36,X37,X38)|X36!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X36!=k1_relset_1(X36,X37,X38)|v1_funct_2(X38,X36,X37)|X36!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))))&((~v1_funct_2(X38,X36,X37)|X38=k1_xboole_0|X36=k1_xboole_0|X37!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X38!=k1_xboole_0|v1_funct_2(X38,X36,X37)|X36=k1_xboole_0|X37!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 8.10/8.30  fof(c_0_15, plain, ![X33, X34, X35]:(~v1_relat_1(X35)|(~r1_tarski(k1_relat_1(X35),X33)|~r1_tarski(k2_relat_1(X35),X34)|m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 8.10/8.30  fof(c_0_16, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(r1_tarski(k2_relat_1(esk7_0),esk6_0)&(~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,k1_relat_1(esk7_0),esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 8.10/8.30  fof(c_0_17, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 8.10/8.30  cnf(c_0_18, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 8.10/8.30  cnf(c_0_19, plain, (X1=k1_relat_1(esk5_2(X2,X1))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.10/8.30  cnf(c_0_20, plain, (v1_funct_1(esk5_2(X1,X2))|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.10/8.30  cnf(c_0_21, plain, (v1_relat_1(esk5_2(X1,X2))|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.10/8.30  fof(c_0_22, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 8.10/8.30  fof(c_0_23, plain, ![X14]:(~r1_tarski(X14,k1_xboole_0)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 8.10/8.30  cnf(c_0_24, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 8.10/8.30  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 8.10/8.30  cnf(c_0_26, negated_conjecture, (~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,k1_relat_1(esk7_0),esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.10/8.30  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.10/8.30  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 8.10/8.30  fof(c_0_29, plain, ![X28, X29]:(~r2_hidden(X28,X29)|~r1_tarski(X29,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 8.10/8.30  cnf(c_0_30, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).
% 8.10/8.30  cnf(c_0_31, plain, (k1_relat_1(esk5_2(X1,k1_xboole_0))=k1_xboole_0), inference(er,[status(thm)],[c_0_19])).
% 8.10/8.30  cnf(c_0_32, plain, (v1_funct_1(esk5_2(X1,k1_xboole_0))), inference(er,[status(thm)],[c_0_20])).
% 8.10/8.30  cnf(c_0_33, plain, (v1_relat_1(esk5_2(X1,k1_xboole_0))), inference(er,[status(thm)],[c_0_21])).
% 8.10/8.30  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 8.10/8.30  cnf(c_0_35, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 8.10/8.30  cnf(c_0_36, plain, (r1_tarski(k2_relat_1(esk5_2(X1,X2)),X1)|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.10/8.30  cnf(c_0_37, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X1)|~r1_tarski(k1_relat_1(X2),X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 8.10/8.30  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.10/8.30  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.10/8.30  fof(c_0_40, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k1_relset_1(X30,X31,X32)=k1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 8.10/8.30  cnf(c_0_41, negated_conjecture, (~v1_funct_2(esk7_0,k1_relat_1(esk7_0),esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])])).
% 8.10/8.30  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 8.10/8.30  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 8.10/8.30  cnf(c_0_44, plain, (r2_hidden(k1_funct_1(esk5_2(X1,k1_xboole_0),X2),k2_relat_1(esk5_2(X1,k1_xboole_0)))|~r2_hidden(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])])).
% 8.10/8.30  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 8.10/8.30  cnf(c_0_46, plain, (r1_tarski(k2_relat_1(esk5_2(X1,k1_xboole_0)),X1)), inference(er,[status(thm)],[c_0_36])).
% 8.10/8.30  cnf(c_0_47, negated_conjecture, (esk6_0=k1_xboole_0|v1_funct_2(esk7_0,X1,esk6_0)|k1_relset_1(X1,esk6_0,esk7_0)!=X1|~r1_tarski(k1_relat_1(esk7_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 8.10/8.30  cnf(c_0_48, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 8.10/8.30  cnf(c_0_49, negated_conjecture, (~v1_funct_2(esk7_0,k1_relat_1(esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_25]), c_0_39]), c_0_38]), c_0_42])])).
% 8.10/8.30  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_35])).
% 8.10/8.30  cnf(c_0_51, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_tarski(k2_relat_1(esk5_2(X2,k1_xboole_0)),k1_funct_1(esk5_2(X2,k1_xboole_0),X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 8.10/8.30  cnf(c_0_52, plain, (r1_tarski(k2_relat_1(esk5_2(k1_xboole_0,k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 8.10/8.30  cnf(c_0_53, negated_conjecture, (esk6_0=k1_xboole_0|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48])]), c_0_42])]), c_0_49])).
% 8.10/8.30  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,esk6_0)|~r1_tarski(k2_relat_1(esk7_0),k1_xboole_0)|~r1_tarski(X1,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_38, c_0_50])).
% 8.10/8.30  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 8.10/8.30  cnf(c_0_56, plain, (r1_tarski(k2_relat_1(esk5_2(X1,X2)),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.10/8.30  cnf(c_0_57, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 8.10/8.30  cnf(c_0_58, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 8.10/8.30  fof(c_0_59, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 8.10/8.30  cnf(c_0_60, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),k1_xboole_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0)))), inference(spm,[status(thm)],[c_0_38, c_0_53])).
% 8.10/8.30  cnf(c_0_61, negated_conjecture, (r1_tarski(X1,esk6_0)|~r1_tarski(k2_relat_1(esk7_0),X2)|~r1_tarski(X1,k2_relat_1(esk7_0))|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_34])])).
% 8.10/8.30  cnf(c_0_62, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),X1)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_50])).
% 8.10/8.30  cnf(c_0_63, plain, (r1_tarski(k2_relat_1(esk5_2(X1,X2)),X1)|r1_tarski(k2_relat_1(esk5_2(X3,X1)),X3)), inference(spm,[status(thm)],[c_0_46, c_0_56])).
% 8.10/8.30  cnf(c_0_64, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_55]), c_0_34])])).
% 8.10/8.30  cnf(c_0_65, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_58])).
% 8.10/8.30  cnf(c_0_66, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 8.10/8.30  cnf(c_0_67, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_25]), c_0_39]), c_0_38]), c_0_42])])).
% 8.10/8.30  cnf(c_0_68, negated_conjecture, (r1_tarski(X1,esk6_0)|~r1_tarski(X1,k2_relat_1(esk7_0))|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(esk6_0,X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 8.10/8.30  cnf(c_0_69, plain, (r1_tarski(k2_relat_1(esk5_2(X1,X1)),X1)), inference(ef,[status(thm)],[c_0_63])).
% 8.10/8.30  cnf(c_0_70, plain, (~r2_hidden(X1,X2)|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_55]), c_0_34])])).
% 8.10/8.30  cnf(c_0_71, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),esk1_2(k2_relat_1(X1),X2)),k1_relat_1(X1))|r1_tarski(k2_relat_1(X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 8.10/8.30  cnf(c_0_72, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(k2_relat_1(X1),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_35]), c_0_57])).
% 8.10/8.30  cnf(c_0_73, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_45, c_0_67])).
% 8.10/8.30  cnf(c_0_74, negated_conjecture, (r1_tarski(k2_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))),esk6_0)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 8.10/8.30  cnf(c_0_75, plain, (~r2_hidden(X1,X2)|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X4,X3)|~r1_tarski(X2,X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_55]), c_0_34])])).
% 8.10/8.30  cnf(c_0_76, plain, (r1_tarski(k2_relat_1(esk5_2(X1,k1_xboole_0)),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_32]), c_0_31]), c_0_33])]), c_0_57])).
% 8.10/8.30  cnf(c_0_77, negated_conjecture, (~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_27]), c_0_39])])).
% 8.10/8.30  cnf(c_0_78, negated_conjecture, (r1_tarski(k2_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))),esk6_0)|~r1_tarski(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_34])).
% 8.10/8.30  cnf(c_0_79, plain, (v1_funct_1(esk5_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.10/8.30  cnf(c_0_80, plain, (v1_relat_1(esk5_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.10/8.30  cnf(c_0_81, plain, (~r2_hidden(X1,X2)|~r1_tarski(X3,k2_relat_1(esk5_2(X4,k1_xboole_0)))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 8.10/8.30  cnf(c_0_82, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_77, c_0_66])).
% 8.10/8.30  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))),k1_xboole_0)|~r1_tarski(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_35]), c_0_34])])).
% 8.10/8.30  cnf(c_0_84, plain, (v1_funct_1(esk5_2(X1,X2))|v1_funct_1(esk5_2(X3,X1))), inference(spm,[status(thm)],[c_0_32, c_0_79])).
% 8.10/8.30  cnf(c_0_85, plain, (v1_relat_1(esk5_2(X1,X2))|v1_relat_1(esk5_2(X3,X1))), inference(spm,[status(thm)],[c_0_33, c_0_80])).
% 8.10/8.30  cnf(c_0_86, negated_conjecture, (~r2_hidden(X1,X2)|~r1_tarski(X2,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 8.10/8.30  cnf(c_0_87, negated_conjecture, (r1_tarski(k2_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))),X1)|~r1_tarski(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_83])).
% 8.10/8.30  cnf(c_0_88, plain, (v1_funct_1(esk5_2(X1,X1))), inference(ef,[status(thm)],[c_0_84])).
% 8.10/8.30  cnf(c_0_89, plain, (v1_relat_1(esk5_2(X1,X1))), inference(ef,[status(thm)],[c_0_85])).
% 8.10/8.30  cnf(c_0_90, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk5_2(k1_relat_1(esk7_0),k1_relat_1(esk7_0))))), inference(spm,[status(thm)],[c_0_86, c_0_69])).
% 8.10/8.30  cnf(c_0_91, negated_conjecture, (~r2_hidden(X1,k1_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))))|~r1_tarski(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_87]), c_0_88]), c_0_89])])).
% 8.10/8.30  cnf(c_0_92, negated_conjecture, (r1_tarski(k2_relat_1(esk5_2(k1_relat_1(esk7_0),k1_relat_1(esk7_0))),X1)), inference(spm,[status(thm)],[c_0_90, c_0_66])).
% 8.10/8.30  cnf(c_0_93, negated_conjecture, (~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk7_0),esk6_0)))|~r2_hidden(X1,k1_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_53]), c_0_34])])).
% 8.10/8.30  cnf(c_0_94, plain, (X1=k1_relat_1(esk5_2(X2,X1))|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.10/8.30  cnf(c_0_95, negated_conjecture, (~r2_hidden(X1,k1_relat_1(esk5_2(k1_relat_1(esk7_0),k1_relat_1(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_92]), c_0_88]), c_0_89])])).
% 8.10/8.30  cnf(c_0_96, negated_conjecture, (~r2_hidden(X1,k1_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_25]), c_0_39]), c_0_73]), c_0_42])])).
% 8.10/8.30  cnf(c_0_97, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 8.10/8.30  cnf(c_0_98, plain, (X1=k1_xboole_0|X2=X3|~r1_tarski(k1_relat_1(esk5_2(X1,X3)),X2)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_94, c_0_50])).
% 8.10/8.30  cnf(c_0_99, negated_conjecture, (r1_tarski(k1_relat_1(esk5_2(k1_relat_1(esk7_0),k1_relat_1(esk7_0))),X1)), inference(spm,[status(thm)],[c_0_95, c_0_66])).
% 8.10/8.30  cnf(c_0_100, negated_conjecture, (r1_tarski(k1_relat_1(esk5_2(k2_relat_1(esk7_0),k2_relat_1(esk7_0))),X1)), inference(spm,[status(thm)],[c_0_96, c_0_66])).
% 8.10/8.30  cnf(c_0_101, negated_conjecture, (~v1_funct_2(esk7_0,k1_xboole_0,esk6_0)|~r1_tarski(k1_relat_1(esk7_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_35])).
% 8.10/8.30  cnf(c_0_102, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_97])).
% 8.10/8.30  cnf(c_0_103, negated_conjecture, (k1_relat_1(esk7_0)=k1_xboole_0|X1=k1_relat_1(esk7_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 8.10/8.30  cnf(c_0_104, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|X1=k2_relat_1(esk7_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_100])).
% 8.10/8.30  cnf(c_0_105, negated_conjecture, (~v1_funct_2(esk7_0,X1,esk6_0)|~r1_tarski(k1_relat_1(esk7_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_55]), c_0_34])])).
% 8.10/8.30  cnf(c_0_106, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_102, c_0_25])).
% 8.10/8.30  cnf(c_0_107, negated_conjecture, (k1_relat_1(esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_103, c_0_34])).
% 8.10/8.30  cnf(c_0_108, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_104, c_0_34])).
% 8.10/8.30  cnf(c_0_109, negated_conjecture, (~v1_funct_2(esk7_0,X1,esk6_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_82])])).
% 8.10/8.30  cnf(c_0_110, negated_conjecture, (v1_funct_2(esk7_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,esk7_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_39]), c_0_34]), c_0_108]), c_0_34])])).
% 8.10/8.30  cnf(c_0_111, negated_conjecture, (~v1_funct_2(X1,X2,esk6_0)|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,esk7_0)|~r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_109, c_0_55])).
% 8.10/8.30  cnf(c_0_112, negated_conjecture, (v1_funct_2(esk7_0,k1_xboole_0,X1)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_48]), c_0_107])])).
% 8.10/8.30  cnf(c_0_113, negated_conjecture, (~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_34]), c_0_42])])).
% 8.10/8.30  cnf(c_0_114, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_25]), c_0_39]), c_0_73]), c_0_82])]), ['proof']).
% 8.10/8.30  # SZS output end CNFRefutation
% 8.10/8.30  # Proof object total steps             : 115
% 8.10/8.30  # Proof object clause steps            : 92
% 8.10/8.30  # Proof object formula steps           : 23
% 8.10/8.30  # Proof object conjectures             : 45
% 8.10/8.30  # Proof object clause conjectures      : 42
% 8.10/8.30  # Proof object formula conjectures     : 3
% 8.10/8.30  # Proof object initial clauses used    : 24
% 8.10/8.30  # Proof object initial formulas used   : 11
% 8.10/8.30  # Proof object generating inferences   : 58
% 8.10/8.30  # Proof object simplifying inferences  : 76
% 8.10/8.30  # Training examples: 0 positive, 0 negative
% 8.10/8.30  # Parsed axioms                        : 11
% 8.10/8.30  # Removed by relevancy pruning/SinE    : 0
% 8.10/8.30  # Initial clauses                      : 35
% 8.10/8.30  # Removed in clause preprocessing      : 0
% 8.10/8.30  # Initial clauses in saturation        : 35
% 8.10/8.30  # Processed clauses                    : 23476
% 8.10/8.30  # ...of these trivial                  : 7
% 8.10/8.30  # ...subsumed                          : 19526
% 8.10/8.30  # ...remaining for further processing  : 3943
% 8.10/8.30  # Other redundant clauses eliminated   : 2438
% 8.10/8.30  # Clauses deleted for lack of memory   : 0
% 8.10/8.30  # Backward-subsumed                    : 1002
% 8.10/8.30  # Backward-rewritten                   : 555
% 8.10/8.30  # Generated clauses                    : 1138208
% 8.10/8.30  # ...of the previous two non-trivial   : 1126692
% 8.10/8.30  # Contextual simplify-reflections      : 196
% 8.10/8.30  # Paramodulations                      : 1135201
% 8.10/8.30  # Factorizations                       : 571
% 8.10/8.30  # Equation resolutions                 : 2438
% 8.10/8.30  # Propositional unsat checks           : 0
% 8.10/8.30  #    Propositional check models        : 0
% 8.10/8.30  #    Propositional check unsatisfiable : 0
% 8.10/8.30  #    Propositional clauses             : 0
% 8.10/8.30  #    Propositional clauses after purity: 0
% 8.10/8.30  #    Propositional unsat core size     : 0
% 8.10/8.30  #    Propositional preprocessing time  : 0.000
% 8.10/8.30  #    Propositional encoding time       : 0.000
% 8.10/8.30  #    Propositional solver time         : 0.000
% 8.10/8.30  #    Success case prop preproc time    : 0.000
% 8.10/8.30  #    Success case prop encoding time   : 0.000
% 8.10/8.30  #    Success case prop solver time     : 0.000
% 8.10/8.30  # Current number of processed clauses  : 2339
% 8.10/8.30  #    Positive orientable unit clauses  : 13
% 8.10/8.30  #    Positive unorientable unit clauses: 0
% 8.10/8.30  #    Negative unit clauses             : 11
% 8.10/8.30  #    Non-unit-clauses                  : 2315
% 8.10/8.30  # Current number of unprocessed clauses: 1097697
% 8.10/8.30  # ...number of literals in the above   : 6813570
% 8.10/8.30  # Current number of archived formulas  : 0
% 8.10/8.30  # Current number of archived clauses   : 1591
% 8.10/8.30  # Clause-clause subsumption calls (NU) : 2589620
% 8.10/8.30  # Rec. Clause-clause subsumption calls : 458654
% 8.10/8.30  # Non-unit clause-clause subsumptions  : 17679
% 8.10/8.30  # Unit Clause-clause subsumption calls : 14948
% 8.10/8.30  # Rewrite failures with RHS unbound    : 0
% 8.10/8.30  # BW rewrite match attempts            : 194
% 8.10/8.30  # BW rewrite match successes           : 30
% 8.10/8.30  # Condensation attempts                : 0
% 8.10/8.30  # Condensation successes               : 0
% 8.10/8.30  # Termbank termtop insertions          : 20918946
% 8.10/8.34  
% 8.10/8.34  # -------------------------------------------------
% 8.10/8.34  # User time                : 7.606 s
% 8.10/8.34  # System time              : 0.399 s
% 8.10/8.34  # Total time               : 8.006 s
% 8.10/8.34  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
