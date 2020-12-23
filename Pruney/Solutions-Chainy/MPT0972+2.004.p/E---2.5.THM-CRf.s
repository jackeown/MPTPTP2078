%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 937 expanded)
%              Number of clauses        :   47 ( 377 expanded)
%              Number of leaves         :   10 ( 225 expanded)
%              Depth                    :   16
%              Number of atoms          :  222 (5236 expanded)
%              Number of equality atoms :   80 (1194 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( r2_hidden(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ! [X5] :
                  ( r2_hidden(X5,X1)
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
             => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_2])).

fof(c_0_11,plain,(
    ! [X42,X43,X44] :
      ( ( ~ v1_funct_2(X44,X42,X43)
        | X42 = k1_relset_1(X42,X43,X44)
        | X43 = k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_relset_1(X42,X43,X44)
        | v1_funct_2(X44,X42,X43)
        | X43 = k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( ~ v1_funct_2(X44,X42,X43)
        | X42 = k1_relset_1(X42,X43,X44)
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_relset_1(X42,X43,X44)
        | v1_funct_2(X44,X42,X43)
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( ~ v1_funct_2(X44,X42,X43)
        | X44 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X44 != k1_xboole_0
        | v1_funct_2(X44,X42,X43)
        | X42 = k1_xboole_0
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_12,negated_conjecture,(
    ! [X49] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk6_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk6_0,esk7_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & ( ~ r2_hidden(X49,esk6_0)
        | k1_funct_1(esk8_0,X49) = k1_funct_1(esk9_0,X49) )
      & ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k1_relset_1(X35,X36,X37) = k1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_14,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_19,plain,(
    ! [X23,X24] :
      ( ( r2_hidden(esk5_2(X23,X24),k1_relat_1(X23))
        | k1_relat_1(X23) != k1_relat_1(X24)
        | X23 = X24
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( k1_funct_1(X23,esk5_2(X23,X24)) != k1_funct_1(X24,esk5_2(X23,X24))
        | k1_relat_1(X23) != k1_relat_1(X24)
        | X23 = X24
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_20,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk8_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_21,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk9_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_23]),c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

fof(c_0_31,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_32,plain,(
    ! [X16,X17] :
      ( ( ~ r2_hidden(esk3_2(X16,X17),X16)
        | ~ r2_hidden(esk3_2(X16,X17),X17)
        | X16 = X17 )
      & ( r2_hidden(esk3_2(X16,X17),X16)
        | r2_hidden(esk3_2(X16,X17),X17)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_33,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = X1
    | r2_hidden(esk5_2(esk8_0,X1),esk6_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_xboole_0(X32)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X32)))
      | v1_xboole_0(X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_40,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk5_2(X1,X2)) != k1_funct_1(X2,esk5_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = k1_funct_1(esk9_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk5_2(esk8_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_43,plain,
    ( X1 = X2
    | r2_hidden(esk3_2(X1,X2),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | X1 = esk9_0
    | k1_funct_1(X1,esk5_2(X1,esk9_0)) != k1_funct_1(esk9_0,esk5_2(X1,esk9_0))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0)) = k1_funct_1(esk8_0,esk5_2(esk8_0,esk9_0))
    | esk7_0 = k1_xboole_0
    | esk9_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_47,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | r2_relset_1(X38,X39,X40,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_43])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_27]),c_0_28])]),c_0_46])).

cnf(c_0_52,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( esk9_0 = esk8_0
    | v1_xboole_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_49])])).

cnf(c_0_55,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(condense,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_57,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_relset_1(esk6_0,esk7_0,esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_15])).

cnf(c_0_61,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_relset_1(esk6_0,esk7_0,esk8_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_49])]),c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( r2_relset_1(esk6_0,esk7_0,esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_23])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_relset_1(esk6_0,esk7_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_59]),c_0_59]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.38  # and selection function SelectNewComplexAHPNS.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.023 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t18_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 0.19/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.38  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 0.19/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.38  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.19/0.38  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.19/0.38  fof(reflexivity_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_relset_1(X1,X2,X3,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 0.19/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4))))), inference(assume_negation,[status(cth)],[t18_funct_2])).
% 0.19/0.38  fof(c_0_11, plain, ![X42, X43, X44]:((((~v1_funct_2(X44,X42,X43)|X42=k1_relset_1(X42,X43,X44)|X43=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X42!=k1_relset_1(X42,X43,X44)|v1_funct_2(X44,X42,X43)|X43=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&((~v1_funct_2(X44,X42,X43)|X42=k1_relset_1(X42,X43,X44)|X42!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X42!=k1_relset_1(X42,X43,X44)|v1_funct_2(X44,X42,X43)|X42!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))))&((~v1_funct_2(X44,X42,X43)|X44=k1_xboole_0|X42=k1_xboole_0|X43!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X44!=k1_xboole_0|v1_funct_2(X44,X42,X43)|X42=k1_xboole_0|X43!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.38  fof(c_0_12, negated_conjecture, ![X49]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&((~r2_hidden(X49,esk6_0)|k1_funct_1(esk8_0,X49)=k1_funct_1(esk9_0,X49))&~r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.19/0.38  fof(c_0_13, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k1_relset_1(X35,X36,X37)=k1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.38  cnf(c_0_14, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_18, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.38  fof(c_0_19, plain, ![X23, X24]:((r2_hidden(esk5_2(X23,X24),k1_relat_1(X23))|k1_relat_1(X23)!=k1_relat_1(X24)|X23=X24|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(k1_funct_1(X23,esk5_2(X23,X24))!=k1_funct_1(X24,esk5_2(X23,X24))|k1_relat_1(X23)!=k1_relat_1(X24)|X23=X24|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk8_0)=esk6_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.19/0.38  cnf(c_0_22, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_25, plain, (r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_22, c_0_15])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk9_0)=esk6_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_23]), c_0_24])])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_17, c_0_23])).
% 0.19/0.38  fof(c_0_31, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.38  fof(c_0_32, plain, ![X16, X17]:((~r2_hidden(esk3_2(X16,X17),X16)|~r2_hidden(esk3_2(X16,X17),X17)|X16=X17)&(r2_hidden(esk3_2(X16,X17),X16)|r2_hidden(esk3_2(X16,X17),X17)|X16=X17)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=X1|r2_hidden(esk5_2(esk8_0,X1),esk6_0)|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (k1_relat_1(esk9_0)=esk6_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.38  cnf(c_0_37, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_38, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  fof(c_0_39, plain, ![X32, X33, X34]:(~v1_xboole_0(X32)|(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X32)))|v1_xboole_0(X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.19/0.38  cnf(c_0_40, plain, (X1=X2|k1_funct_1(X1,esk5_2(X1,X2))!=k1_funct_1(X2,esk5_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk8_0,X1)=k1_funct_1(esk9_0,X1)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (esk9_0=esk8_0|esk7_0=k1_xboole_0|r2_hidden(esk5_2(esk8_0,esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.19/0.38  cnf(c_0_43, plain, (X1=X2|r2_hidden(esk3_2(X1,X2),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.38  cnf(c_0_44, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (esk7_0=k1_xboole_0|X1=esk9_0|k1_funct_1(X1,esk5_2(X1,esk9_0))!=k1_funct_1(esk9_0,esk5_2(X1,esk9_0))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_34]), c_0_35]), c_0_36])])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk9_0,esk5_2(esk8_0,esk9_0))=k1_funct_1(esk8_0,esk5_2(esk8_0,esk9_0))|esk7_0=k1_xboole_0|esk9_0=esk8_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  fof(c_0_47, plain, ![X38, X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|r2_relset_1(X38,X39,X40,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).
% 0.19/0.38  cnf(c_0_48, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_37, c_0_43])).
% 0.19/0.38  cnf(c_0_49, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (v1_xboole_0(esk9_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_23])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (esk9_0=esk8_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_26]), c_0_27]), c_0_28])]), c_0_46])).
% 0.19/0.38  cnf(c_0_52, plain, (r2_relset_1(X2,X3,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.38  cnf(c_0_53, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (esk9_0=esk8_0|v1_xboole_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_49])])).
% 0.19/0.38  cnf(c_0_55, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(condense,[status(thm)],[c_0_52])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (~r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (esk9_0=esk8_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (r2_relset_1(esk6_0,esk7_0,esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_55, c_0_15])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_15])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_51, c_0_59])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (~r2_relset_1(esk6_0,esk7_0,esk8_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_56, c_0_59])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_49])]), c_0_53])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (r2_relset_1(esk6_0,esk7_0,esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_55, c_0_23])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (~r2_relset_1(esk6_0,esk7_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_59]), c_0_59]), c_0_65]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 67
% 0.19/0.38  # Proof object clause steps            : 47
% 0.19/0.38  # Proof object formula steps           : 20
% 0.19/0.38  # Proof object conjectures             : 36
% 0.19/0.38  # Proof object clause conjectures      : 33
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 18
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 24
% 0.19/0.38  # Proof object simplifying inferences  : 31
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 14
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 33
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 33
% 0.19/0.38  # Processed clauses                    : 240
% 0.19/0.38  # ...of these trivial                  : 4
% 0.19/0.38  # ...subsumed                          : 74
% 0.19/0.38  # ...remaining for further processing  : 161
% 0.19/0.38  # Other redundant clauses eliminated   : 27
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 13
% 0.19/0.38  # Backward-rewritten                   : 71
% 0.19/0.38  # Generated clauses                    : 527
% 0.19/0.38  # ...of the previous two non-trivial   : 499
% 0.19/0.38  # Contextual simplify-reflections      : 3
% 0.19/0.38  # Paramodulations                      : 496
% 0.19/0.38  # Factorizations                       : 3
% 0.19/0.38  # Equation resolutions                 : 29
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
% 0.19/0.38  # Current number of processed clauses  : 73
% 0.19/0.38  #    Positive orientable unit clauses  : 21
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 50
% 0.19/0.38  # Current number of unprocessed clauses: 270
% 0.19/0.38  # ...number of literals in the above   : 1126
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 84
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2267
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 1135
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 109
% 0.19/0.38  # Unit Clause-clause subsumption calls : 272
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 30
% 0.19/0.38  # BW rewrite match successes           : 7
% 0.19/0.38  # Condensation attempts                : 240
% 0.19/0.38  # Condensation successes               : 20
% 0.19/0.38  # Termbank termtop insertions          : 10147
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.007 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
