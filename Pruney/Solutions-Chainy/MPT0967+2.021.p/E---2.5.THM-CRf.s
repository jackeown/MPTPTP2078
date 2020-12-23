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
% DateTime   : Thu Dec  3 11:01:24 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 804 expanded)
%              Number of clauses        :   91 ( 354 expanded)
%              Number of leaves         :   21 ( 204 expanded)
%              Depth                    :   18
%              Number of atoms          :  373 (3177 expanded)
%              Number of equality atoms :  125 ( 900 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc10_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

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

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_23,plain,(
    ! [X45] :
      ( ~ v1_xboole_0(X45)
      | v1_xboole_0(k1_relat_1(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

fof(c_0_24,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_25,plain,(
    ! [X30,X31,X32] :
      ( ( r1_tarski(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))
        | ~ r1_tarski(X30,X31) )
      & ( r1_tarski(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31))
        | ~ r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_26,plain,(
    ! [X52,X53,X54] :
      ( ( ~ v1_funct_2(X54,X52,X53)
        | X52 = k1_relset_1(X52,X53,X54)
        | X53 = k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X52 != k1_relset_1(X52,X53,X54)
        | v1_funct_2(X54,X52,X53)
        | X53 = k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( ~ v1_funct_2(X54,X52,X53)
        | X52 = k1_relset_1(X52,X53,X54)
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X52 != k1_relset_1(X52,X53,X54)
        | v1_funct_2(X54,X52,X53)
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( ~ v1_funct_2(X54,X52,X53)
        | X54 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X54 != k1_xboole_0
        | v1_funct_2(X54,X52,X53)
        | X52 = k1_xboole_0
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_27,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & r1_tarski(esk6_0,esk7_0)
    & ( esk6_0 != k1_xboole_0
      | esk5_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk8_0)
      | ~ v1_funct_2(esk8_0,esk5_0,esk7_0)
      | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_28,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | k1_relset_1(X49,X50,X51) = k1_relat_1(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r2_hidden(esk3_2(X16,X17),X16)
        | r1_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_2(X16,X17),X17)
        | r1_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_32,plain,(
    ! [X25] :
      ( ( r1_xboole_0(X25,X25)
        | X25 != k1_xboole_0 )
      & ( X25 = k1_xboole_0
        | ~ r1_xboole_0(X25,X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X28,X29] :
      ( ( k2_zfmisc_1(X28,X29) != k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0 )
      & ( X28 != k1_xboole_0
        | k2_zfmisc_1(X28,X29) = k1_xboole_0 )
      & ( X29 != k1_xboole_0
        | k2_zfmisc_1(X28,X29) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_36,plain,(
    ! [X24] : r1_tarski(k1_xboole_0,X24) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_37,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_48,plain,(
    ! [X42,X43,X44] :
      ( ~ r2_hidden(X42,X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(X44))
      | m1_subset_1(X42,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_49,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X40,k1_zfmisc_1(X41))
        | r1_tarski(X40,X41) )
      & ( ~ r1_tarski(X40,X41)
        | m1_subset_1(X40,k1_zfmisc_1(X41)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_50,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X38,X39)
      | v1_xboole_0(X39)
      | r2_hidden(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_51,plain,(
    ! [X35] : ~ v1_xboole_0(k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_52,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_53,plain,
    ( k1_relset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_55,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X3 != k1_xboole_0
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

fof(c_0_58,plain,(
    ! [X26,X27] :
      ( ~ v1_xboole_0(X26)
      | X26 = X27
      | ~ v1_xboole_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_59,plain,(
    ! [X36,X37] :
      ( ~ v1_xboole_0(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | v1_xboole_0(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_62,plain,(
    ! [X33,X34] :
      ( ~ r1_tarski(X33,X34)
      | r1_tarski(k1_zfmisc_1(X33),k1_zfmisc_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ v1_xboole_0(esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_38])]),c_0_54])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_47])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_38]),c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk8_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_76,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_30])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_38])).

cnf(c_0_78,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_1(esk8_0)
    | ~ v1_funct_2(esk8_0,esk5_0,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk8_0,k1_zfmisc_1(k1_xboole_0))
    | esk8_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_84,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk8_0,k1_zfmisc_1(k1_xboole_0))
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_75])).

cnf(c_0_86,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_66])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_75]),c_0_78])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_38])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_funct_2(esk8_0,esk5_0,esk7_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(X1))
    | esk8_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_47])])).

cnf(c_0_91,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relat_1(X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_40])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(X1))
    | esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_85]),c_0_47])])).

cnf(c_0_93,negated_conjecture,
    ( X1 = k1_relat_1(esk8_0)
    | esk6_0 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk8_0,k1_xboole_0)
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_75])).

cnf(c_0_95,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_96,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | ~ v1_funct_2(esk8_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_2(esk8_0,X1,X2)
    | esk6_0 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_94]),c_0_47])])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk8_0,k1_zfmisc_1(k1_xboole_0))
    | esk5_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_46])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_46]),c_0_78])])).

cnf(c_0_101,plain,
    ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_73]),c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(X1))
    | esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_99]),c_0_47])])).

cnf(c_0_104,negated_conjecture,
    ( X1 = k1_relat_1(esk8_0)
    | esk5_0 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_100])).

fof(c_0_105,plain,(
    ! [X46,X47,X48] :
      ( ~ v1_xboole_0(X46)
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))
      | v1_xboole_0(X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_106,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X3 != k1_xboole_0
    | ~ r1_tarski(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_75]),c_0_47])])).

cnf(c_0_107,plain,
    ( v1_xboole_0(k1_relset_1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_40])).

cnf(c_0_108,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = esk5_0 ),
    inference(sr,[status(thm)],[c_0_52,c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ v1_funct_2(esk8_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( v1_funct_2(esk8_0,X1,X2)
    | esk5_0 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_103]),c_0_104])).

cnf(c_0_111,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_112,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_106,c_0_47])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_72])).

cnf(c_0_114,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_38])])).

cnf(c_0_115,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_116,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_111,c_0_61])).

cnf(c_0_117,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_112])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_95])).

cnf(c_0_119,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_114]),c_0_115])).

cnf(c_0_120,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_78])])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,X1))
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( ~ r1_tarski(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_123,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_40])).

cnf(c_0_124,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_125,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r1_tarski(esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_75]),c_0_122])).

cnf(c_0_126,plain,
    ( k1_relset_1(X1,X2,X3) = X4
    | X5 = k1_xboole_0
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_128,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,X1)
    | k1_relset_1(esk5_0,X1,esk8_0) != esk5_0
    | ~ r1_tarski(esk6_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_118]),c_0_125])).

cnf(c_0_129,negated_conjecture,
    ( k1_relset_1(X1,X2,esk8_0) = esk5_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_38]),c_0_39])]),c_0_102])).

cnf(c_0_130,negated_conjecture,
    ( ~ v1_funct_2(esk8_0,esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_118]),c_0_127])])).

cnf(c_0_131,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_118])).

cnf(c_0_132,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_127])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:57:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.62/0.79  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.62/0.79  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.62/0.79  #
% 0.62/0.79  # Preprocessing time       : 0.029 s
% 0.62/0.79  
% 0.62/0.79  # Proof found!
% 0.62/0.79  # SZS status Theorem
% 0.62/0.79  # SZS output start CNFRefutation
% 0.62/0.79  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 0.62/0.79  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.62/0.79  fof(fc10_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k1_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 0.62/0.79  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.62/0.79  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.62/0.79  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.62/0.79  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.62/0.79  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.62/0.79  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.62/0.79  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.62/0.79  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.62/0.79  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.62/0.79  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.62/0.79  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.62/0.79  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.62/0.79  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.62/0.79  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.62/0.79  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.62/0.79  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.62/0.79  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.62/0.79  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.62/0.79  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 0.62/0.79  fof(c_0_22, plain, ![X15]:(~v1_xboole_0(X15)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.62/0.79  fof(c_0_23, plain, ![X45]:(~v1_xboole_0(X45)|v1_xboole_0(k1_relat_1(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).
% 0.62/0.79  fof(c_0_24, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.62/0.79  fof(c_0_25, plain, ![X30, X31, X32]:((r1_tarski(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))|~r1_tarski(X30,X31))&(r1_tarski(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31))|~r1_tarski(X30,X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.62/0.79  fof(c_0_26, plain, ![X52, X53, X54]:((((~v1_funct_2(X54,X52,X53)|X52=k1_relset_1(X52,X53,X54)|X53=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X52!=k1_relset_1(X52,X53,X54)|v1_funct_2(X54,X52,X53)|X53=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&((~v1_funct_2(X54,X52,X53)|X52=k1_relset_1(X52,X53,X54)|X52!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X52!=k1_relset_1(X52,X53,X54)|v1_funct_2(X54,X52,X53)|X52!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))))&((~v1_funct_2(X54,X52,X53)|X54=k1_xboole_0|X52=k1_xboole_0|X53!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X54!=k1_xboole_0|v1_funct_2(X54,X52,X53)|X52=k1_xboole_0|X53!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.62/0.79  fof(c_0_27, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r1_tarski(esk6_0,esk7_0)&((esk6_0!=k1_xboole_0|esk5_0=k1_xboole_0)&(~v1_funct_1(esk8_0)|~v1_funct_2(esk8_0,esk5_0,esk7_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.62/0.79  fof(c_0_28, plain, ![X49, X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|k1_relset_1(X49,X50,X51)=k1_relat_1(X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.62/0.79  cnf(c_0_29, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.62/0.79  cnf(c_0_30, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.62/0.79  fof(c_0_31, plain, ![X16, X17, X19, X20, X21]:(((r2_hidden(esk3_2(X16,X17),X16)|r1_xboole_0(X16,X17))&(r2_hidden(esk3_2(X16,X17),X17)|r1_xboole_0(X16,X17)))&(~r2_hidden(X21,X19)|~r2_hidden(X21,X20)|~r1_xboole_0(X19,X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.62/0.79  fof(c_0_32, plain, ![X25]:((r1_xboole_0(X25,X25)|X25!=k1_xboole_0)&(X25=k1_xboole_0|~r1_xboole_0(X25,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.62/0.79  cnf(c_0_33, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.62/0.79  cnf(c_0_34, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.62/0.79  fof(c_0_35, plain, ![X28, X29]:((k2_zfmisc_1(X28,X29)!=k1_xboole_0|(X28=k1_xboole_0|X29=k1_xboole_0))&((X28!=k1_xboole_0|k2_zfmisc_1(X28,X29)=k1_xboole_0)&(X29!=k1_xboole_0|k2_zfmisc_1(X28,X29)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.62/0.79  fof(c_0_36, plain, ![X24]:r1_tarski(k1_xboole_0,X24), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.62/0.79  cnf(c_0_37, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.62/0.79  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.62/0.79  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.62/0.79  cnf(c_0_40, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.62/0.79  cnf(c_0_41, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.62/0.79  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.62/0.79  cnf(c_0_43, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.62/0.79  fof(c_0_44, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.62/0.79  cnf(c_0_45, plain, (k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X2)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.62/0.79  cnf(c_0_46, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.62/0.79  cnf(c_0_47, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.62/0.79  fof(c_0_48, plain, ![X42, X43, X44]:(~r2_hidden(X42,X43)|~m1_subset_1(X43,k1_zfmisc_1(X44))|m1_subset_1(X42,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.62/0.79  fof(c_0_49, plain, ![X40, X41]:((~m1_subset_1(X40,k1_zfmisc_1(X41))|r1_tarski(X40,X41))&(~r1_tarski(X40,X41)|m1_subset_1(X40,k1_zfmisc_1(X41)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.62/0.79  fof(c_0_50, plain, ![X38, X39]:(~m1_subset_1(X38,X39)|(v1_xboole_0(X39)|r2_hidden(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.62/0.79  fof(c_0_51, plain, ![X35]:~v1_xboole_0(k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.62/0.79  cnf(c_0_52, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.62/0.79  cnf(c_0_53, plain, (k1_relset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.62/0.79  cnf(c_0_54, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.62/0.79  cnf(c_0_55, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.62/0.79  cnf(c_0_56, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.62/0.79  cnf(c_0_57, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X3!=k1_xboole_0|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.62/0.79  fof(c_0_58, plain, ![X26, X27]:(~v1_xboole_0(X26)|X26=X27|~v1_xboole_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.62/0.79  fof(c_0_59, plain, ![X36, X37]:(~v1_xboole_0(X36)|(~m1_subset_1(X37,k1_zfmisc_1(X36))|v1_xboole_0(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.62/0.79  cnf(c_0_60, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.62/0.79  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.62/0.79  fof(c_0_62, plain, ![X33, X34]:(~r1_tarski(X33,X34)|r1_tarski(k1_zfmisc_1(X33),k1_zfmisc_1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.62/0.79  cnf(c_0_63, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.62/0.79  cnf(c_0_64, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.62/0.79  cnf(c_0_65, negated_conjecture, (esk5_0=k1_xboole_0|~v1_xboole_0(esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_38])]), c_0_54])).
% 0.62/0.79  cnf(c_0_66, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.62/0.79  cnf(c_0_67, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_47])).
% 0.62/0.79  cnf(c_0_68, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.62/0.79  cnf(c_0_69, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.62/0.79  cnf(c_0_70, plain, (m1_subset_1(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.62/0.79  cnf(c_0_71, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.62/0.79  cnf(c_0_72, negated_conjecture, (r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_38]), c_0_64])).
% 0.62/0.79  cnf(c_0_73, negated_conjecture, (esk5_0=k1_xboole_0|esk8_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.62/0.79  cnf(c_0_74, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_67])).
% 0.62/0.79  cnf(c_0_75, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.62/0.79  cnf(c_0_76, plain, (X1=k1_relat_1(X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_68, c_0_30])).
% 0.62/0.79  cnf(c_0_77, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_69, c_0_38])).
% 0.62/0.79  cnf(c_0_78, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.62/0.79  cnf(c_0_79, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.62/0.79  cnf(c_0_80, negated_conjecture, (~v1_funct_1(esk8_0)|~v1_funct_2(esk8_0,esk5_0,esk7_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.62/0.79  cnf(c_0_81, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.62/0.79  cnf(c_0_82, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X3,X2)|~r2_hidden(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.62/0.79  cnf(c_0_83, negated_conjecture, (r2_hidden(esk8_0,k1_zfmisc_1(k1_xboole_0))|esk8_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.62/0.79  cnf(c_0_84, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.62/0.79  cnf(c_0_85, negated_conjecture, (r2_hidden(esk8_0,k1_zfmisc_1(k1_xboole_0))|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_75])).
% 0.62/0.79  cnf(c_0_86, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_76, c_0_66])).
% 0.62/0.79  cnf(c_0_87, negated_conjecture, (v1_xboole_0(esk8_0)|esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_75]), c_0_78])])).
% 0.62/0.79  cnf(c_0_88, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_79, c_0_38])).
% 0.62/0.79  cnf(c_0_89, negated_conjecture, (~v1_funct_2(esk8_0,esk5_0,esk7_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.62/0.79  cnf(c_0_90, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(X1))|esk8_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_47])])).
% 0.62/0.79  cnf(c_0_91, plain, (v1_funct_2(X1,X2,X3)|k1_relat_1(X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_84, c_0_40])).
% 0.62/0.79  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(X1))|esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_85]), c_0_47])])).
% 0.62/0.79  cnf(c_0_93, negated_conjecture, (X1=k1_relat_1(esk8_0)|esk6_0!=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.62/0.79  cnf(c_0_94, negated_conjecture, (r1_tarski(esk8_0,k1_xboole_0)|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_75])).
% 0.62/0.79  cnf(c_0_95, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.62/0.79  cnf(c_0_96, negated_conjecture, (esk8_0!=k1_xboole_0|~v1_funct_2(esk8_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.62/0.79  cnf(c_0_97, negated_conjecture, (v1_funct_2(esk8_0,X1,X2)|esk6_0!=k1_xboole_0|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 0.62/0.79  cnf(c_0_98, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_94]), c_0_47])])).
% 0.62/0.79  cnf(c_0_99, negated_conjecture, (r2_hidden(esk8_0,k1_zfmisc_1(k1_xboole_0))|esk5_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_46])).
% 0.62/0.79  cnf(c_0_100, negated_conjecture, (v1_xboole_0(esk8_0)|esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_46]), c_0_78])])).
% 0.62/0.79  cnf(c_0_101, plain, (k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_33, c_0_95])).
% 0.62/0.79  cnf(c_0_102, negated_conjecture, (esk6_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_73]), c_0_98])).
% 0.62/0.79  cnf(c_0_103, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(X1))|esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_99]), c_0_47])])).
% 0.62/0.79  cnf(c_0_104, negated_conjecture, (X1=k1_relat_1(esk8_0)|esk5_0!=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_86, c_0_100])).
% 0.62/0.79  fof(c_0_105, plain, ![X46, X47, X48]:(~v1_xboole_0(X46)|(~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))|v1_xboole_0(X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.62/0.79  cnf(c_0_106, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X3!=k1_xboole_0|~r1_tarski(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_75]), c_0_47])])).
% 0.62/0.79  cnf(c_0_107, plain, (v1_xboole_0(k1_relset_1(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_30, c_0_40])).
% 0.62/0.79  cnf(c_0_108, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=esk5_0), inference(sr,[status(thm)],[c_0_52, c_0_102])).
% 0.62/0.79  cnf(c_0_109, negated_conjecture, (esk5_0!=k1_xboole_0|~v1_funct_2(esk8_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_89, c_0_103])).
% 0.62/0.79  cnf(c_0_110, negated_conjecture, (v1_funct_2(esk8_0,X1,X2)|esk5_0!=k1_xboole_0|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_103]), c_0_104])).
% 0.62/0.79  cnf(c_0_111, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.62/0.79  cnf(c_0_112, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_106, c_0_47])).
% 0.62/0.79  cnf(c_0_113, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(X1))|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_82, c_0_72])).
% 0.62/0.79  cnf(c_0_114, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_38])])).
% 0.62/0.79  cnf(c_0_115, negated_conjecture, (esk5_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.62/0.79  cnf(c_0_116, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_111, c_0_61])).
% 0.62/0.79  cnf(c_0_117, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_112])).
% 0.62/0.79  cnf(c_0_118, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_113, c_0_95])).
% 0.62/0.79  cnf(c_0_119, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_114]), c_0_115])).
% 0.62/0.79  cnf(c_0_120, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_78])])).
% 0.62/0.79  cnf(c_0_121, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,X1))|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_79, c_0_118])).
% 0.62/0.79  cnf(c_0_122, negated_conjecture, (~r1_tarski(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 0.62/0.79  cnf(c_0_123, plain, (k1_relset_1(X1,X2,X3)=k1_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_40, c_0_40])).
% 0.62/0.79  cnf(c_0_124, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.62/0.79  cnf(c_0_125, negated_conjecture, (X1!=k1_xboole_0|~r1_tarski(esk6_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_75]), c_0_122])).
% 0.62/0.79  cnf(c_0_126, plain, (k1_relset_1(X1,X2,X3)=X4|X5=k1_xboole_0|~v1_funct_2(X3,X4,X5)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_123])).
% 0.62/0.79  cnf(c_0_127, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.62/0.79  cnf(c_0_128, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,X1)|k1_relset_1(esk5_0,X1,esk8_0)!=esk5_0|~r1_tarski(esk6_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_118]), c_0_125])).
% 0.62/0.79  cnf(c_0_129, negated_conjecture, (k1_relset_1(X1,X2,esk8_0)=esk5_0|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_38]), c_0_39])]), c_0_102])).
% 0.62/0.79  cnf(c_0_130, negated_conjecture, (~v1_funct_2(esk8_0,esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_118]), c_0_127])])).
% 0.62/0.79  cnf(c_0_131, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,X1)|~r1_tarski(esk6_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_118])).
% 0.62/0.79  cnf(c_0_132, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_127])]), ['proof']).
% 0.62/0.79  # SZS output end CNFRefutation
% 0.62/0.79  # Proof object total steps             : 133
% 0.62/0.79  # Proof object clause steps            : 91
% 0.62/0.79  # Proof object formula steps           : 42
% 0.62/0.79  # Proof object conjectures             : 47
% 0.62/0.79  # Proof object clause conjectures      : 44
% 0.62/0.79  # Proof object formula conjectures     : 3
% 0.62/0.79  # Proof object initial clauses used    : 31
% 0.62/0.79  # Proof object initial formulas used   : 21
% 0.62/0.79  # Proof object generating inferences   : 58
% 0.62/0.79  # Proof object simplifying inferences  : 45
% 0.62/0.79  # Training examples: 0 positive, 0 negative
% 0.62/0.79  # Parsed axioms                        : 23
% 0.62/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.79  # Initial clauses                      : 50
% 0.62/0.79  # Removed in clause preprocessing      : 0
% 0.62/0.79  # Initial clauses in saturation        : 50
% 0.62/0.79  # Processed clauses                    : 6049
% 0.62/0.79  # ...of these trivial                  : 95
% 0.62/0.79  # ...subsumed                          : 4824
% 0.62/0.79  # ...remaining for further processing  : 1130
% 0.62/0.79  # Other redundant clauses eliminated   : 24
% 0.62/0.79  # Clauses deleted for lack of memory   : 0
% 0.62/0.79  # Backward-subsumed                    : 116
% 0.62/0.79  # Backward-rewritten                   : 28
% 0.62/0.79  # Generated clauses                    : 34841
% 0.62/0.79  # ...of the previous two non-trivial   : 28964
% 0.62/0.79  # Contextual simplify-reflections      : 56
% 0.62/0.79  # Paramodulations                      : 34660
% 0.62/0.79  # Factorizations                       : 128
% 0.62/0.79  # Equation resolutions                 : 50
% 0.62/0.79  # Propositional unsat checks           : 0
% 0.62/0.79  #    Propositional check models        : 0
% 0.62/0.79  #    Propositional check unsatisfiable : 0
% 0.62/0.79  #    Propositional clauses             : 0
% 0.62/0.79  #    Propositional clauses after purity: 0
% 0.62/0.79  #    Propositional unsat core size     : 0
% 0.62/0.79  #    Propositional preprocessing time  : 0.000
% 0.62/0.79  #    Propositional encoding time       : 0.000
% 0.62/0.79  #    Propositional solver time         : 0.000
% 0.62/0.79  #    Success case prop preproc time    : 0.000
% 0.62/0.79  #    Success case prop encoding time   : 0.000
% 0.62/0.79  #    Success case prop solver time     : 0.000
% 0.62/0.79  # Current number of processed clauses  : 981
% 0.62/0.79  #    Positive orientable unit clauses  : 41
% 0.62/0.79  #    Positive unorientable unit clauses: 0
% 0.62/0.79  #    Negative unit clauses             : 22
% 0.62/0.79  #    Non-unit-clauses                  : 918
% 0.62/0.79  # Current number of unprocessed clauses: 22460
% 0.62/0.79  # ...number of literals in the above   : 81160
% 0.62/0.79  # Current number of archived formulas  : 0
% 0.62/0.79  # Current number of archived clauses   : 147
% 0.62/0.79  # Clause-clause subsumption calls (NU) : 53693
% 0.62/0.79  # Rec. Clause-clause subsumption calls : 42199
% 0.62/0.79  # Non-unit clause-clause subsumptions  : 1800
% 0.62/0.79  # Unit Clause-clause subsumption calls : 2709
% 0.62/0.79  # Rewrite failures with RHS unbound    : 0
% 0.62/0.79  # BW rewrite match attempts            : 72
% 0.62/0.79  # BW rewrite match successes           : 23
% 0.62/0.79  # Condensation attempts                : 0
% 0.62/0.79  # Condensation successes               : 0
% 0.62/0.79  # Termbank termtop insertions          : 390178
% 0.62/0.79  
% 0.62/0.79  # -------------------------------------------------
% 0.62/0.79  # User time                : 0.446 s
% 0.62/0.79  # System time              : 0.016 s
% 0.62/0.79  # Total time               : 0.462 s
% 0.62/0.79  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
