%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:28 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 418 expanded)
%              Number of clauses        :   64 ( 161 expanded)
%              Number of leaves         :   26 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :  369 (1960 expanded)
%              Number of equality atoms :   65 ( 119 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
           => ( v2_funct_1(X3)
              & v2_funct_2(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t26_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
           => ( ( X3 = k1_xboole_0
                & X2 != k1_xboole_0 )
              | v2_funct_1(X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
             => ( v2_funct_1(X3)
                & v2_funct_2(X4,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_funct_2])).

fof(c_0_27,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk4_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))
    & r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0))
    & ( ~ v2_funct_1(esk6_0)
      | ~ v2_funct_2(esk7_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_28,plain,(
    ! [X68] : k6_partfun1(X68) = k6_relat_1(X68) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_29,plain,(
    ! [X40,X41,X42] :
      ( ( v4_relat_1(X42,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( v5_relat_1(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_30,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | v1_relat_1(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_31,plain,(
    ! [X29,X30] : v1_relat_1(k2_zfmisc_1(X29,X30)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_32,plain,(
    ! [X49,X50,X51,X52] :
      ( ( ~ r2_relset_1(X49,X50,X51,X52)
        | X51 = X52
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X51 != X52
        | r2_relset_1(X49,X50,X51,X52)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X53] : m1_subset_1(k6_relat_1(X53),k1_zfmisc_1(k2_zfmisc_1(X53,X53))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

fof(c_0_36,plain,(
    ! [X26,X27] :
      ( ( ~ v5_relat_1(X27,X26)
        | r1_tarski(k2_relat_1(X27),X26)
        | ~ v1_relat_1(X27) )
      & ( ~ r1_tarski(k2_relat_1(X27),X26)
        | v5_relat_1(X27,X26)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_37,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_relat_1(X32)
      | r1_tarski(k2_relat_1(k5_relat_1(X31,X32)),k2_relat_1(X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

fof(c_0_42,plain,(
    ! [X62,X63,X64,X65,X66,X67] :
      ( ~ v1_funct_1(X66)
      | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))
      | ~ v1_funct_1(X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
      | k1_partfun1(X62,X63,X64,X65,X66,X67) = k5_relat_1(X66,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_43,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_46,plain,(
    ! [X56,X57,X58,X59,X60,X61] :
      ( ( v1_funct_1(k1_partfun1(X56,X57,X58,X59,X60,X61))
        | ~ v1_funct_1(X60)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_funct_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) )
      & ( m1_subset_1(k1_partfun1(X56,X57,X58,X59,X60,X61),k1_zfmisc_1(k2_zfmisc_1(X56,X59)))
        | ~ v1_funct_1(X60)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_funct_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_47,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_48,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( v5_relat_1(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_40])])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0) = k6_relat_1(esk4_0)
    | ~ m1_subset_1(k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_59,plain,(
    ! [X33] :
      ( k1_relat_1(k6_relat_1(X33)) = X33
      & k2_relat_1(k6_relat_1(X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_60,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v2_funct_1(X34)
        | ~ r2_hidden(X35,k1_relat_1(X34))
        | ~ r2_hidden(X36,k1_relat_1(X34))
        | k1_funct_1(X34,X35) != k1_funct_1(X34,X36)
        | X35 = X36
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( r2_hidden(esk2_1(X34),k1_relat_1(X34))
        | v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( r2_hidden(esk3_1(X34),k1_relat_1(X34))
        | v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( k1_funct_1(X34,esk2_1(X34)) = k1_funct_1(X34,esk3_1(X34))
        | v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( esk2_1(X34) != esk3_1(X34)
        | v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

fof(c_0_61,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_62,plain,(
    ! [X28] :
      ( ~ v1_xboole_0(X28)
      | v1_xboole_0(k1_relat_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

fof(c_0_63,plain,(
    ! [X20,X21] : ~ r2_hidden(X20,k2_zfmisc_1(X20,X21)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_65,plain,(
    ! [X54,X55] :
      ( ( ~ v2_funct_2(X55,X54)
        | k2_relat_1(X55) = X54
        | ~ v1_relat_1(X55)
        | ~ v5_relat_1(X55,X54) )
      & ( k2_relat_1(X55) != X54
        | v2_funct_2(X55,X54)
        | ~ v1_relat_1(X55)
        | ~ v5_relat_1(X55,X54) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_66,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_68,plain,
    ( r1_tarski(k2_relat_1(k1_partfun1(X1,X2,X3,X4,X5,X6)),k2_relat_1(X6))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0) = k6_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),c_0_38]),c_0_58])])).

cnf(c_0_70,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_58]),c_0_40])])).

cnf(c_0_72,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_64])).

fof(c_0_77,plain,(
    ! [X43,X44,X45] :
      ( ~ v1_xboole_0(X43)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | v1_xboole_0(X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_78,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk4_0
    | ~ r1_tarski(esk4_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk4_0,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_56]),c_0_57]),c_0_51]),c_0_71]),c_0_38]),c_0_58])])).

fof(c_0_81,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X13,X12)
        | r1_tarski(X13,X11)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r1_tarski(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r2_hidden(esk1_2(X15,X16),X16)
        | ~ r1_tarski(esk1_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) )
      & ( r2_hidden(esk1_2(X15,X16),X16)
        | r1_tarski(esk1_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_82,negated_conjecture,
    ( v2_funct_1(esk6_0)
    | r2_hidden(esk2_1(esk6_0),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_57]),c_0_71])])).

cnf(c_0_83,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_86,plain,(
    ! [X46,X47,X48] :
      ( ~ v1_xboole_0(X46)
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))
      | v1_xboole_0(X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_87,plain,(
    ! [X69,X70,X71,X72,X73] :
      ( ( X71 = k1_xboole_0
        | v2_funct_1(X72)
        | ~ v2_funct_1(k1_partfun1(X69,X70,X70,X71,X72,X73))
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,X70,X71)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_2(X72,X69,X70)
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) )
      & ( X70 != k1_xboole_0
        | v2_funct_1(X72)
        | ~ v2_funct_1(k1_partfun1(X69,X70,X70,X71,X72,X73))
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,X70,X71)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
        | ~ v1_funct_1(X72)
        | ~ v1_funct_2(X72,X69,X70)
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).

fof(c_0_88,plain,(
    ! [X39] :
      ( v1_relat_1(k6_relat_1(X39))
      & v2_funct_1(k6_relat_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_89,plain,
    ( v2_funct_2(X1,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_90,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

fof(c_0_91,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | m1_subset_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( v2_funct_1(esk6_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_58])).

cnf(c_0_95,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_96,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_97,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_100,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_101,negated_conjecture,
    ( ~ v2_funct_1(esk6_0)
    | ~ v2_funct_2(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_102,negated_conjecture,
    ( v2_funct_2(esk7_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_50]),c_0_51])])).

cnf(c_0_103,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_106,negated_conjecture,
    ( v2_funct_1(esk6_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_107,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_76]),c_0_96])])).

cnf(c_0_108,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_69]),c_0_98]),c_0_99]),c_0_100]),c_0_56]),c_0_57]),c_0_38]),c_0_58])])).

cnf(c_0_109,negated_conjecture,
    ( ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102])])).

cnf(c_0_110,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_111,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_105])).

cnf(c_0_112,negated_conjecture,
    ( v2_funct_1(esk6_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( k1_xboole_0 = esk4_0 ),
    inference(sr,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_114,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113]),c_0_114])]),c_0_109]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:36:27 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.16/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.38  #
% 0.16/0.38  # Preprocessing time       : 0.030 s
% 0.16/0.38  # Presaturation interreduction done
% 0.16/0.38  
% 0.16/0.38  # Proof found!
% 0.16/0.38  # SZS status Theorem
% 0.16/0.38  # SZS output start CNFRefutation
% 0.16/0.38  fof(t29_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 0.16/0.38  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.16/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.16/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.16/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.16/0.38  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.16/0.38  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.16/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.16/0.38  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 0.16/0.38  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.16/0.38  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.16/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.16/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.16/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.16/0.38  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.16/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.16/0.38  fof(fc10_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k1_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 0.16/0.38  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.16/0.38  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.16/0.38  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.16/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.16/0.38  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.16/0.38  fof(t26_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))=>((X3=k1_xboole_0&X2!=k1_xboole_0)|v2_funct_1(X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 0.16/0.38  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.16/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.16/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.16/0.38  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1)))))), inference(assume_negation,[status(cth)],[t29_funct_2])).
% 0.16/0.38  fof(c_0_27, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk4_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))))&(r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0))&(~v2_funct_1(esk6_0)|~v2_funct_2(esk7_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.16/0.38  fof(c_0_28, plain, ![X68]:k6_partfun1(X68)=k6_relat_1(X68), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.16/0.38  fof(c_0_29, plain, ![X40, X41, X42]:((v4_relat_1(X42,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(v5_relat_1(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.16/0.38  fof(c_0_30, plain, ![X24, X25]:(~v1_relat_1(X24)|(~m1_subset_1(X25,k1_zfmisc_1(X24))|v1_relat_1(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.16/0.38  fof(c_0_31, plain, ![X29, X30]:v1_relat_1(k2_zfmisc_1(X29,X30)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.16/0.38  fof(c_0_32, plain, ![X49, X50, X51, X52]:((~r2_relset_1(X49,X50,X51,X52)|X51=X52|(~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))&(X51!=X52|r2_relset_1(X49,X50,X51,X52)|(~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.16/0.38  cnf(c_0_33, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_partfun1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.38  cnf(c_0_34, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.16/0.38  fof(c_0_35, plain, ![X53]:m1_subset_1(k6_relat_1(X53),k1_zfmisc_1(k2_zfmisc_1(X53,X53))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.16/0.38  fof(c_0_36, plain, ![X26, X27]:((~v5_relat_1(X27,X26)|r1_tarski(k2_relat_1(X27),X26)|~v1_relat_1(X27))&(~r1_tarski(k2_relat_1(X27),X26)|v5_relat_1(X27,X26)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.16/0.38  cnf(c_0_37, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.16/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.38  cnf(c_0_39, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.16/0.38  cnf(c_0_40, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.38  fof(c_0_41, plain, ![X31, X32]:(~v1_relat_1(X31)|(~v1_relat_1(X32)|r1_tarski(k2_relat_1(k5_relat_1(X31,X32)),k2_relat_1(X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.16/0.38  fof(c_0_42, plain, ![X62, X63, X64, X65, X66, X67]:(~v1_funct_1(X66)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))|~v1_funct_1(X67)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))|k1_partfun1(X62,X63,X64,X65,X66,X67)=k5_relat_1(X66,X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.16/0.38  cnf(c_0_43, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.16/0.38  cnf(c_0_44, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k6_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.16/0.38  cnf(c_0_45, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.16/0.38  fof(c_0_46, plain, ![X56, X57, X58, X59, X60, X61]:((v1_funct_1(k1_partfun1(X56,X57,X58,X59,X60,X61))|(~v1_funct_1(X60)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|~v1_funct_1(X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))))&(m1_subset_1(k1_partfun1(X56,X57,X58,X59,X60,X61),k1_zfmisc_1(k2_zfmisc_1(X56,X59)))|(~v1_funct_1(X60)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|~v1_funct_1(X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.16/0.38  fof(c_0_47, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.16/0.38  fof(c_0_48, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.16/0.38  cnf(c_0_49, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.16/0.38  cnf(c_0_50, negated_conjecture, (v5_relat_1(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.16/0.38  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_38]), c_0_40])])).
% 0.16/0.38  cnf(c_0_52, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.16/0.38  cnf(c_0_53, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.16/0.38  cnf(c_0_54, negated_conjecture, (k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0)=k6_relat_1(esk4_0)|~m1_subset_1(k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.16/0.38  cnf(c_0_55, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.16/0.38  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.38  cnf(c_0_57, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.38  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.38  fof(c_0_59, plain, ![X33]:(k1_relat_1(k6_relat_1(X33))=X33&k2_relat_1(k6_relat_1(X33))=X33), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.16/0.38  fof(c_0_60, plain, ![X34, X35, X36]:((~v2_funct_1(X34)|(~r2_hidden(X35,k1_relat_1(X34))|~r2_hidden(X36,k1_relat_1(X34))|k1_funct_1(X34,X35)!=k1_funct_1(X34,X36)|X35=X36)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&((((r2_hidden(esk2_1(X34),k1_relat_1(X34))|v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(r2_hidden(esk3_1(X34),k1_relat_1(X34))|v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34))))&(k1_funct_1(X34,esk2_1(X34))=k1_funct_1(X34,esk3_1(X34))|v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34))))&(esk2_1(X34)!=esk3_1(X34)|v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.16/0.38  fof(c_0_61, plain, ![X7]:(~v1_xboole_0(X7)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.16/0.38  fof(c_0_62, plain, ![X28]:(~v1_xboole_0(X28)|v1_xboole_0(k1_relat_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).
% 0.16/0.38  fof(c_0_63, plain, ![X20, X21]:~r2_hidden(X20,k2_zfmisc_1(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.16/0.38  cnf(c_0_64, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.16/0.38  fof(c_0_65, plain, ![X54, X55]:((~v2_funct_2(X55,X54)|k2_relat_1(X55)=X54|(~v1_relat_1(X55)|~v5_relat_1(X55,X54)))&(k2_relat_1(X55)!=X54|v2_funct_2(X55,X54)|(~v1_relat_1(X55)|~v5_relat_1(X55,X54)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.16/0.38  cnf(c_0_66, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.16/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.16/0.38  cnf(c_0_68, plain, (r1_tarski(k2_relat_1(k1_partfun1(X1,X2,X3,X4,X5,X6)),k2_relat_1(X6))|~v1_funct_1(X6)|~v1_funct_1(X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.16/0.38  cnf(c_0_69, negated_conjecture, (k1_partfun1(esk4_0,esk5_0,esk5_0,esk4_0,esk6_0,esk7_0)=k6_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), c_0_38]), c_0_58])])).
% 0.16/0.38  cnf(c_0_70, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.16/0.38  cnf(c_0_71, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_58]), c_0_40])])).
% 0.16/0.38  cnf(c_0_72, plain, (r2_hidden(esk2_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.16/0.38  cnf(c_0_73, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.16/0.38  cnf(c_0_74, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.16/0.38  cnf(c_0_75, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.16/0.38  cnf(c_0_76, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_64])).
% 0.16/0.38  fof(c_0_77, plain, ![X43, X44, X45]:(~v1_xboole_0(X43)|(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_xboole_0(X45))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.16/0.38  cnf(c_0_78, plain, (v2_funct_2(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.16/0.38  cnf(c_0_79, negated_conjecture, (k2_relat_1(esk7_0)=esk4_0|~r1_tarski(esk4_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.16/0.38  cnf(c_0_80, negated_conjecture, (r1_tarski(esk4_0,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_56]), c_0_57]), c_0_51]), c_0_71]), c_0_38]), c_0_58])])).
% 0.16/0.38  fof(c_0_81, plain, ![X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X13,X12)|r1_tarski(X13,X11)|X12!=k1_zfmisc_1(X11))&(~r1_tarski(X14,X11)|r2_hidden(X14,X12)|X12!=k1_zfmisc_1(X11)))&((~r2_hidden(esk1_2(X15,X16),X16)|~r1_tarski(esk1_2(X15,X16),X15)|X16=k1_zfmisc_1(X15))&(r2_hidden(esk1_2(X15,X16),X16)|r1_tarski(esk1_2(X15,X16),X15)|X16=k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.16/0.38  cnf(c_0_82, negated_conjecture, (v2_funct_1(esk6_0)|r2_hidden(esk2_1(esk6_0),k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_57]), c_0_71])])).
% 0.16/0.38  cnf(c_0_83, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.16/0.38  cnf(c_0_84, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.16/0.38  cnf(c_0_85, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.16/0.38  fof(c_0_86, plain, ![X46, X47, X48]:(~v1_xboole_0(X46)|(~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))|v1_xboole_0(X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.16/0.38  fof(c_0_87, plain, ![X69, X70, X71, X72, X73]:((X71=k1_xboole_0|v2_funct_1(X72)|~v2_funct_1(k1_partfun1(X69,X70,X70,X71,X72,X73))|(~v1_funct_1(X73)|~v1_funct_2(X73,X70,X71)|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X70,X71))))|(~v1_funct_1(X72)|~v1_funct_2(X72,X69,X70)|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))))&(X70!=k1_xboole_0|v2_funct_1(X72)|~v2_funct_1(k1_partfun1(X69,X70,X70,X71,X72,X73))|(~v1_funct_1(X73)|~v1_funct_2(X73,X70,X71)|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X70,X71))))|(~v1_funct_1(X72)|~v1_funct_2(X72,X69,X70)|~m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).
% 0.16/0.38  fof(c_0_88, plain, ![X39]:(v1_relat_1(k6_relat_1(X39))&v2_funct_1(k6_relat_1(X39))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.16/0.38  cnf(c_0_89, plain, (v2_funct_2(X1,k2_relat_1(X1))|~v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_78])).
% 0.16/0.38  cnf(c_0_90, negated_conjecture, (k2_relat_1(esk7_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.16/0.38  fof(c_0_91, plain, ![X22, X23]:(~r2_hidden(X22,X23)|m1_subset_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.16/0.38  cnf(c_0_92, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.16/0.38  cnf(c_0_93, negated_conjecture, (v2_funct_1(esk6_0)|~v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.16/0.38  cnf(c_0_94, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_85, c_0_58])).
% 0.16/0.38  cnf(c_0_95, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.16/0.38  cnf(c_0_96, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.16/0.38  cnf(c_0_97, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.16/0.38  cnf(c_0_98, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.38  cnf(c_0_99, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.38  cnf(c_0_100, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.16/0.38  cnf(c_0_101, negated_conjecture, (~v2_funct_1(esk6_0)|~v2_funct_2(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.38  cnf(c_0_102, negated_conjecture, (v2_funct_2(esk7_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_50]), c_0_51])])).
% 0.16/0.38  cnf(c_0_103, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.16/0.38  cnf(c_0_104, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_92])).
% 0.16/0.38  cnf(c_0_105, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.16/0.38  cnf(c_0_106, negated_conjecture, (v2_funct_1(esk6_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.16/0.38  cnf(c_0_107, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_76]), c_0_96])])).
% 0.16/0.38  cnf(c_0_108, negated_conjecture, (k1_xboole_0=esk4_0|v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_69]), c_0_98]), c_0_99]), c_0_100]), c_0_56]), c_0_57]), c_0_38]), c_0_58])])).
% 0.16/0.38  cnf(c_0_109, negated_conjecture, (~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102])])).
% 0.16/0.38  cnf(c_0_110, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.16/0.38  cnf(c_0_111, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_105])).
% 0.16/0.38  cnf(c_0_112, negated_conjecture, (v2_funct_1(esk6_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.16/0.38  cnf(c_0_113, negated_conjecture, (k1_xboole_0=esk4_0), inference(sr,[status(thm)],[c_0_108, c_0_109])).
% 0.16/0.38  cnf(c_0_114, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.16/0.38  cnf(c_0_115, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113]), c_0_114])]), c_0_109]), ['proof']).
% 0.16/0.38  # SZS output end CNFRefutation
% 0.16/0.38  # Proof object total steps             : 116
% 0.16/0.38  # Proof object clause steps            : 64
% 0.16/0.38  # Proof object formula steps           : 52
% 0.16/0.38  # Proof object conjectures             : 31
% 0.16/0.38  # Proof object clause conjectures      : 28
% 0.16/0.38  # Proof object formula conjectures     : 3
% 0.16/0.38  # Proof object initial clauses used    : 34
% 0.16/0.38  # Proof object initial formulas used   : 26
% 0.16/0.38  # Proof object generating inferences   : 21
% 0.16/0.38  # Proof object simplifying inferences  : 51
% 0.16/0.38  # Training examples: 0 positive, 0 negative
% 0.16/0.38  # Parsed axioms                        : 27
% 0.16/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.38  # Initial clauses                      : 53
% 0.16/0.38  # Removed in clause preprocessing      : 1
% 0.16/0.38  # Initial clauses in saturation        : 52
% 0.16/0.38  # Processed clauses                    : 370
% 0.16/0.38  # ...of these trivial                  : 5
% 0.16/0.38  # ...subsumed                          : 54
% 0.16/0.38  # ...remaining for further processing  : 311
% 0.16/0.38  # Other redundant clauses eliminated   : 9
% 0.16/0.38  # Clauses deleted for lack of memory   : 0
% 0.16/0.38  # Backward-subsumed                    : 1
% 0.16/0.38  # Backward-rewritten                   : 151
% 0.16/0.38  # Generated clauses                    : 643
% 0.16/0.38  # ...of the previous two non-trivial   : 488
% 0.16/0.38  # Contextual simplify-reflections      : 1
% 0.16/0.38  # Paramodulations                      : 625
% 0.16/0.38  # Factorizations                       : 2
% 0.16/0.38  # Equation resolutions                 : 10
% 0.16/0.38  # Propositional unsat checks           : 0
% 0.16/0.38  #    Propositional check models        : 0
% 0.16/0.38  #    Propositional check unsatisfiable : 0
% 0.16/0.38  #    Propositional clauses             : 0
% 0.16/0.38  #    Propositional clauses after purity: 0
% 0.16/0.38  #    Propositional unsat core size     : 0
% 0.16/0.38  #    Propositional preprocessing time  : 0.000
% 0.16/0.38  #    Propositional encoding time       : 0.000
% 0.16/0.38  #    Propositional solver time         : 0.000
% 0.16/0.38  #    Success case prop preproc time    : 0.000
% 0.16/0.38  #    Success case prop encoding time   : 0.000
% 0.16/0.38  #    Success case prop solver time     : 0.000
% 0.16/0.38  # Current number of processed clauses  : 93
% 0.16/0.38  #    Positive orientable unit clauses  : 33
% 0.16/0.38  #    Positive unorientable unit clauses: 0
% 0.16/0.38  #    Negative unit clauses             : 2
% 0.16/0.38  #    Non-unit-clauses                  : 58
% 0.16/0.38  # Current number of unprocessed clauses: 184
% 0.16/0.38  # ...number of literals in the above   : 615
% 0.16/0.38  # Current number of archived formulas  : 0
% 0.16/0.38  # Current number of archived clauses   : 210
% 0.16/0.38  # Clause-clause subsumption calls (NU) : 12786
% 0.16/0.38  # Rec. Clause-clause subsumption calls : 8203
% 0.16/0.38  # Non-unit clause-clause subsumptions  : 52
% 0.16/0.38  # Unit Clause-clause subsumption calls : 340
% 0.16/0.38  # Rewrite failures with RHS unbound    : 0
% 0.16/0.38  # BW rewrite match attempts            : 33
% 0.16/0.38  # BW rewrite match successes           : 9
% 0.16/0.38  # Condensation attempts                : 0
% 0.16/0.38  # Condensation successes               : 0
% 0.16/0.38  # Termbank termtop insertions          : 13981
% 0.16/0.38  
% 0.16/0.38  # -------------------------------------------------
% 0.16/0.38  # User time                : 0.053 s
% 0.16/0.38  # System time              : 0.008 s
% 0.16/0.38  # Total time               : 0.061 s
% 0.16/0.38  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
