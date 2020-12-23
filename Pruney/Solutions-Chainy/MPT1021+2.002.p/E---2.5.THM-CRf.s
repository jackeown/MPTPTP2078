%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:06 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  145 (2339 expanded)
%              Number of clauses        :   87 ( 854 expanded)
%              Number of leaves         :   29 ( 577 expanded)
%              Depth                    :   13
%              Number of atoms          :  417 (9847 expanded)
%              Number of equality atoms :   96 ( 628 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
        & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(dt_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v1_funct_1(k2_funct_2(X1,X2))
        & v1_funct_2(k2_funct_2(X1,X2),X1,X1)
        & v3_funct_2(k2_funct_2(X1,X2),X1,X1)
        & m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t35_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
          & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t88_funct_2])).

fof(c_0_30,plain,(
    ! [X86,X87,X88] :
      ( ( v1_funct_1(X88)
        | ~ v1_funct_1(X88)
        | ~ v3_funct_2(X88,X86,X87)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) )
      & ( v2_funct_1(X88)
        | ~ v1_funct_1(X88)
        | ~ v3_funct_2(X88,X86,X87)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) )
      & ( v2_funct_2(X88,X87)
        | ~ v1_funct_1(X88)
        | ~ v3_funct_2(X88,X86,X87)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_31,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk4_0,esk4_0)
    & v3_funct_2(esk5_0,esk4_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & ( ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_partfun1(esk4_0))
      | ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_partfun1(esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_32,plain,(
    ! [X65,X66,X67] :
      ( ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
      | v1_relat_1(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_33,plain,(
    ! [X68,X69,X70] :
      ( ( v4_relat_1(X70,X68)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( v5_relat_1(X70,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_34,plain,(
    ! [X59] :
      ( ( k5_relat_1(X59,k2_funct_1(X59)) = k6_relat_1(k1_relat_1(X59))
        | ~ v2_funct_1(X59)
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) )
      & ( k5_relat_1(k2_funct_1(X59),X59) = k6_relat_1(k2_relat_1(X59))
        | ~ v2_funct_1(X59)
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_35,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( v3_funct_2(esk5_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X92,X93] :
      ( ( ~ v2_funct_2(X93,X92)
        | k2_relat_1(X93) = X92
        | ~ v1_relat_1(X93)
        | ~ v5_relat_1(X93,X92) )
      & ( k2_relat_1(X93) != X92
        | v2_funct_2(X93,X92)
        | ~ v1_relat_1(X93)
        | ~ v5_relat_1(X93,X92) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_41,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | ~ v1_xboole_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_44,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_45,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_48,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( v2_funct_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_50,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

fof(c_0_51,plain,(
    ! [X103,X104] :
      ( ~ v1_funct_1(X104)
      | ~ v1_funct_2(X104,X103,X103)
      | ~ v3_funct_2(X104,X103,X103)
      | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X103,X103)))
      | k2_funct_2(X103,X104) = k2_funct_1(X104) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_52,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X53)
      | k2_relat_1(k7_relat_1(X53,X52)) = k9_relat_1(X53,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_53,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X55)
      | ~ v4_relat_1(X55,X54)
      | X55 = k7_relat_1(X55,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_54,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_57,plain,(
    ! [X97,X98,X99,X100,X101,X102] :
      ( ~ v1_funct_1(X101)
      | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X97,X98)))
      | ~ v1_funct_1(X102)
      | ~ m1_subset_1(X102,k1_zfmisc_1(k2_zfmisc_1(X99,X100)))
      | k1_partfun1(X97,X98,X99,X100,X101,X102) = k5_relat_1(X101,X102) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_58,plain,(
    ! [X94,X95] :
      ( ( v1_funct_1(k2_funct_2(X94,X95))
        | ~ v1_funct_1(X95)
        | ~ v1_funct_2(X95,X94,X94)
        | ~ v3_funct_2(X95,X94,X94)
        | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(X94,X94))) )
      & ( v1_funct_2(k2_funct_2(X94,X95),X94,X94)
        | ~ v1_funct_1(X95)
        | ~ v1_funct_2(X95,X94,X94)
        | ~ v3_funct_2(X95,X94,X94)
        | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(X94,X94))) )
      & ( v3_funct_2(k2_funct_2(X94,X95),X94,X94)
        | ~ v1_funct_1(X95)
        | ~ v1_funct_2(X95,X94,X94)
        | ~ v3_funct_2(X95,X94,X94)
        | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(X94,X94))) )
      & ( m1_subset_1(k2_funct_2(X94,X95),k1_zfmisc_1(k2_zfmisc_1(X94,X94)))
        | ~ v1_funct_1(X95)
        | ~ v1_funct_2(X95,X94,X94)
        | ~ v3_funct_2(X95,X94,X94)
        | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(X94,X94))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

cnf(c_0_59,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),esk5_0) = k6_relat_1(k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_37]),c_0_47])])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_47])])).

cnf(c_0_61,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_63,plain,(
    ! [X75,X76,X77,X78] :
      ( ( ~ r2_relset_1(X75,X76,X77,X78)
        | X77 = X78
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X75,X76))) )
      & ( X77 != X78
        | r2_relset_1(X75,X76,X77,X78)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))
        | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X75,X76))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_64,plain,(
    ! [X96] :
      ( v1_partfun1(k6_partfun1(X96),X96)
      & m1_subset_1(k6_partfun1(X96),k1_zfmisc_1(k2_zfmisc_1(X96,X96))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_65,plain,(
    ! [X105] : k6_partfun1(X105) = k6_relat_1(X105) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_66,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( v4_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_38])).

fof(c_0_69,plain,(
    ! [X71,X72,X73,X74] :
      ( ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X72)))
      | k7_relset_1(X71,X72,X73,X74) = k9_relat_1(X73,X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_70,plain,(
    ! [X80,X81,X82] :
      ( ( k7_relset_1(X80,X81,X82,X80) = k2_relset_1(X80,X81,X82)
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( k8_relset_1(X80,X81,X82,X81) = k1_relset_1(X80,X81,X82)
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_71,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | ~ r2_xboole_0(X17,X18) )
      & ( X17 != X18
        | ~ r2_xboole_0(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | X17 = X18
        | r2_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_73,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_74,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_75,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_76,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),esk5_0) = k6_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_77,negated_conjecture,
    ( k2_funct_1(esk5_0) = k2_funct_2(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_78,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_79,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_80,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_81,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_82,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_83,plain,(
    ! [X106,X107,X108] :
      ( ( k5_relat_1(X108,k2_funct_1(X108)) = k6_partfun1(X106)
        | X107 = k1_xboole_0
        | k2_relset_1(X106,X107,X108) != X107
        | ~ v2_funct_1(X108)
        | ~ v1_funct_1(X108)
        | ~ v1_funct_2(X108,X106,X107)
        | ~ m1_subset_1(X108,k1_zfmisc_1(k2_zfmisc_1(X106,X107))) )
      & ( k5_relat_1(k2_funct_1(X108),X108) = k6_partfun1(X107)
        | X107 = k1_xboole_0
        | k2_relset_1(X106,X107,X108) != X107
        | ~ v2_funct_1(X108)
        | ~ v1_funct_1(X108)
        | ~ v1_funct_2(X108,X106,X107)
        | ~ m1_subset_1(X108,k1_zfmisc_1(k2_zfmisc_1(X106,X107))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

cnf(c_0_84,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk5_0,X1)) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_47])).

cnf(c_0_85,negated_conjecture,
    ( k7_relat_1(esk5_0,esk4_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_47])])).

cnf(c_0_86,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_87,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_88,plain,(
    ! [X41,X42,X43] :
      ( ~ r2_hidden(X41,X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(X43))
      | ~ v1_xboole_0(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_89,plain,(
    ! [X20,X21] :
      ( ( r2_hidden(esk3_2(X20,X21),X21)
        | ~ r2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_2(X20,X21),X20)
        | ~ r2_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

cnf(c_0_90,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_91,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_partfun1(esk4_0))
    | ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_partfun1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_93,negated_conjecture,
    ( k1_partfun1(X1,X2,esk4_0,esk4_0,X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_38]),c_0_37])])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k2_funct_2(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_62]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_95,negated_conjecture,
    ( k5_relat_1(k2_funct_2(esk4_0,esk5_0),esk5_0) = k6_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_1(k2_funct_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_62]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_97,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_98,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_99,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_46]),c_0_37]),c_0_47])])).

cnf(c_0_100,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_101,negated_conjecture,
    ( k9_relat_1(esk5_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_60])).

cnf(c_0_102,negated_conjecture,
    ( k9_relat_1(esk5_0,X1) = k7_relset_1(esk4_0,esk4_0,esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_38])).

cnf(c_0_103,negated_conjecture,
    ( k7_relset_1(esk4_0,esk4_0,esk5_0,esk4_0) = k2_relset_1(esk4_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_38])).

fof(c_0_104,plain,(
    ! [X49] :
      ( v1_xboole_0(X49)
      | ~ v1_relat_1(X49)
      | ~ v1_xboole_0(k2_relat_1(X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

fof(c_0_105,plain,(
    ! [X57] :
      ( k1_relat_1(k6_relat_1(X57)) = X57
      & k2_relat_1(k6_relat_1(X57)) = X57 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_106,plain,(
    ! [X58] :
      ( v1_relat_1(k6_relat_1(X58))
      & v1_funct_1(k6_relat_1(X58)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_107,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_108,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_109,plain,
    ( k1_xboole_0 = X1
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_110,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_relat_1(esk4_0))
    | ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_81]),c_0_81])).

cnf(c_0_111,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0) = k6_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_96])])).

cnf(c_0_112,plain,
    ( r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_113,negated_conjecture,
    ( k1_partfun1(X1,X2,esk4_0,esk4_0,X3,k2_funct_2(esk4_0,esk5_0)) = k5_relat_1(X3,k2_funct_2(esk4_0,esk5_0))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_94]),c_0_96])])).

cnf(c_0_114,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_2(esk4_0,esk5_0)) = k6_relat_1(k1_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_99,c_0_77])).

cnf(c_0_115,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_100,c_0_81])).

cnf(c_0_116,negated_conjecture,
    ( k2_relset_1(esk4_0,esk4_0,esk5_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102]),c_0_103])).

fof(c_0_117,plain,(
    ! [X19] :
      ( ~ v1_xboole_0(X19)
      | X19 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_118,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_119,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_120,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_121,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_38])).

cnf(c_0_122,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

fof(c_0_123,plain,(
    ! [X32,X33] :
      ( ~ v1_xboole_0(X33)
      | v1_xboole_0(k2_zfmisc_1(X32,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_124,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_112])])).

cnf(c_0_125,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)) = k6_relat_1(k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_38]),c_0_114]),c_0_37])])).

cnf(c_0_126,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk5_0)) = k6_relat_1(esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_77]),c_0_114]),c_0_62]),c_0_46]),c_0_37]),c_0_38])])).

cnf(c_0_127,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_128,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120])])).

fof(c_0_129,plain,(
    ! [X39,X40] :
      ( ( ~ m1_subset_1(X39,k1_zfmisc_1(X40))
        | r1_tarski(X39,X40) )
      & ( ~ r1_tarski(X39,X40)
        | m1_subset_1(X39,k1_zfmisc_1(X40)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_130,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_131,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_132,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,k6_relat_1(k1_relat_1(esk5_0)),k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_133,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_126]),c_0_119])).

cnf(c_0_134,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_135,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_136,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_137,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_112])])).

cnf(c_0_138,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_139,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_134,c_0_73])).

cnf(c_0_140,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_135,c_0_91])).

cnf(c_0_141,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_137]),c_0_73])])).

cnf(c_0_142,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_143,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_137]),c_0_137]),c_0_137]),c_0_139]),c_0_141]),c_0_142]),c_0_139]),c_0_143])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.63  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.47/0.63  # and selection function SelectCQArNTNpEqFirst.
% 0.47/0.63  #
% 0.47/0.63  # Preprocessing time       : 0.031 s
% 0.47/0.63  # Presaturation interreduction done
% 0.47/0.63  
% 0.47/0.63  # Proof found!
% 0.47/0.63  # SZS status Theorem
% 0.47/0.63  # SZS output start CNFRefutation
% 0.47/0.63  fof(t88_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 0.47/0.63  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.47/0.63  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.47/0.63  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.47/0.63  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.47/0.63  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.47/0.63  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 0.47/0.63  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.47/0.63  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.47/0.63  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.47/0.63  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.47/0.63  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.47/0.63  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 0.47/0.63  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.47/0.63  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.47/0.63  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.47/0.63  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.47/0.63  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 0.47/0.63  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.47/0.63  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.47/0.63  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 0.47/0.63  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.47/0.63  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 0.47/0.63  fof(fc9_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 0.47/0.63  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.47/0.63  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.47/0.63  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.47/0.63  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.47/0.63  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.47/0.63  fof(c_0_29, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1))))), inference(assume_negation,[status(cth)],[t88_funct_2])).
% 0.47/0.63  fof(c_0_30, plain, ![X86, X87, X88]:(((v1_funct_1(X88)|(~v1_funct_1(X88)|~v3_funct_2(X88,X86,X87))|~m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87))))&(v2_funct_1(X88)|(~v1_funct_1(X88)|~v3_funct_2(X88,X86,X87))|~m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87)))))&(v2_funct_2(X88,X87)|(~v1_funct_1(X88)|~v3_funct_2(X88,X86,X87))|~m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.47/0.63  fof(c_0_31, negated_conjecture, ((((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk4_0,esk4_0))&v3_funct_2(esk5_0,esk4_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&(~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_partfun1(esk4_0))|~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_partfun1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.47/0.63  fof(c_0_32, plain, ![X65, X66, X67]:(~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))|v1_relat_1(X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.47/0.63  fof(c_0_33, plain, ![X68, X69, X70]:((v4_relat_1(X70,X68)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))))&(v5_relat_1(X70,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.47/0.63  fof(c_0_34, plain, ![X59]:((k5_relat_1(X59,k2_funct_1(X59))=k6_relat_1(k1_relat_1(X59))|~v2_funct_1(X59)|(~v1_relat_1(X59)|~v1_funct_1(X59)))&(k5_relat_1(k2_funct_1(X59),X59)=k6_relat_1(k2_relat_1(X59))|~v2_funct_1(X59)|(~v1_relat_1(X59)|~v1_funct_1(X59)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.47/0.63  cnf(c_0_35, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.47/0.63  cnf(c_0_36, negated_conjecture, (v3_funct_2(esk5_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.63  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.63  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.63  cnf(c_0_39, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.63  fof(c_0_40, plain, ![X92, X93]:((~v2_funct_2(X93,X92)|k2_relat_1(X93)=X92|(~v1_relat_1(X93)|~v5_relat_1(X93,X92)))&(k2_relat_1(X93)!=X92|v2_funct_2(X93,X92)|(~v1_relat_1(X93)|~v5_relat_1(X93,X92)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.47/0.63  cnf(c_0_41, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.47/0.63  cnf(c_0_42, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.47/0.63  fof(c_0_43, plain, ![X28, X29]:(~r2_hidden(X28,X29)|~v1_xboole_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.47/0.63  fof(c_0_44, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.47/0.63  cnf(c_0_45, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.47/0.63  cnf(c_0_46, negated_conjecture, (v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 0.47/0.63  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.47/0.63  cnf(c_0_48, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.47/0.63  cnf(c_0_49, negated_conjecture, (v2_funct_2(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_36]), c_0_37]), c_0_38])])).
% 0.47/0.63  cnf(c_0_50, negated_conjecture, (v5_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 0.47/0.63  fof(c_0_51, plain, ![X103, X104]:(~v1_funct_1(X104)|~v1_funct_2(X104,X103,X103)|~v3_funct_2(X104,X103,X103)|~m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X103,X103)))|k2_funct_2(X103,X104)=k2_funct_1(X104)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.47/0.63  fof(c_0_52, plain, ![X52, X53]:(~v1_relat_1(X53)|k2_relat_1(k7_relat_1(X53,X52))=k9_relat_1(X53,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.47/0.63  fof(c_0_53, plain, ![X54, X55]:(~v1_relat_1(X55)|~v4_relat_1(X55,X54)|X55=k7_relat_1(X55,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.47/0.63  cnf(c_0_54, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.47/0.63  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.47/0.63  cnf(c_0_56, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.47/0.63  fof(c_0_57, plain, ![X97, X98, X99, X100, X101, X102]:(~v1_funct_1(X101)|~m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X97,X98)))|~v1_funct_1(X102)|~m1_subset_1(X102,k1_zfmisc_1(k2_zfmisc_1(X99,X100)))|k1_partfun1(X97,X98,X99,X100,X101,X102)=k5_relat_1(X101,X102)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.47/0.63  fof(c_0_58, plain, ![X94, X95]:((((v1_funct_1(k2_funct_2(X94,X95))|(~v1_funct_1(X95)|~v1_funct_2(X95,X94,X94)|~v3_funct_2(X95,X94,X94)|~m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(X94,X94)))))&(v1_funct_2(k2_funct_2(X94,X95),X94,X94)|(~v1_funct_1(X95)|~v1_funct_2(X95,X94,X94)|~v3_funct_2(X95,X94,X94)|~m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(X94,X94))))))&(v3_funct_2(k2_funct_2(X94,X95),X94,X94)|(~v1_funct_1(X95)|~v1_funct_2(X95,X94,X94)|~v3_funct_2(X95,X94,X94)|~m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(X94,X94))))))&(m1_subset_1(k2_funct_2(X94,X95),k1_zfmisc_1(k2_zfmisc_1(X94,X94)))|(~v1_funct_1(X95)|~v1_funct_2(X95,X94,X94)|~v3_funct_2(X95,X94,X94)|~m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(X94,X94)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 0.47/0.63  cnf(c_0_59, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),esk5_0)=k6_relat_1(k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_37]), c_0_47])])).
% 0.47/0.63  cnf(c_0_60, negated_conjecture, (k2_relat_1(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_47])])).
% 0.47/0.63  cnf(c_0_61, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.47/0.63  cnf(c_0_62, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.63  fof(c_0_63, plain, ![X75, X76, X77, X78]:((~r2_relset_1(X75,X76,X77,X78)|X77=X78|(~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))|~m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))))&(X77!=X78|r2_relset_1(X75,X76,X77,X78)|(~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))|~m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.47/0.63  fof(c_0_64, plain, ![X96]:(v1_partfun1(k6_partfun1(X96),X96)&m1_subset_1(k6_partfun1(X96),k1_zfmisc_1(k2_zfmisc_1(X96,X96)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.47/0.63  fof(c_0_65, plain, ![X105]:k6_partfun1(X105)=k6_relat_1(X105), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.47/0.63  cnf(c_0_66, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.47/0.63  cnf(c_0_67, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.63  cnf(c_0_68, negated_conjecture, (v4_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_38])).
% 0.47/0.63  fof(c_0_69, plain, ![X71, X72, X73, X74]:(~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X72)))|k7_relset_1(X71,X72,X73,X74)=k9_relat_1(X73,X74)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.47/0.63  fof(c_0_70, plain, ![X80, X81, X82]:((k7_relset_1(X80,X81,X82,X80)=k2_relset_1(X80,X81,X82)|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))&(k8_relset_1(X80,X81,X82,X81)=k1_relset_1(X80,X81,X82)|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.47/0.63  fof(c_0_71, plain, ![X17, X18]:(((r1_tarski(X17,X18)|~r2_xboole_0(X17,X18))&(X17!=X18|~r2_xboole_0(X17,X18)))&(~r1_tarski(X17,X18)|X17=X18|r2_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.47/0.63  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.47/0.63  cnf(c_0_73, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.47/0.63  cnf(c_0_74, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.47/0.63  cnf(c_0_75, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.47/0.63  cnf(c_0_76, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),esk5_0)=k6_relat_1(esk4_0)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.47/0.63  cnf(c_0_77, negated_conjecture, (k2_funct_1(esk5_0)=k2_funct_2(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_36]), c_0_37]), c_0_38])])).
% 0.47/0.63  cnf(c_0_78, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.47/0.63  cnf(c_0_79, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.47/0.63  cnf(c_0_80, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.47/0.63  cnf(c_0_81, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.47/0.63  cnf(c_0_82, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.47/0.63  fof(c_0_83, plain, ![X106, X107, X108]:((k5_relat_1(X108,k2_funct_1(X108))=k6_partfun1(X106)|X107=k1_xboole_0|(k2_relset_1(X106,X107,X108)!=X107|~v2_funct_1(X108))|(~v1_funct_1(X108)|~v1_funct_2(X108,X106,X107)|~m1_subset_1(X108,k1_zfmisc_1(k2_zfmisc_1(X106,X107)))))&(k5_relat_1(k2_funct_1(X108),X108)=k6_partfun1(X107)|X107=k1_xboole_0|(k2_relset_1(X106,X107,X108)!=X107|~v2_funct_1(X108))|(~v1_funct_1(X108)|~v1_funct_2(X108,X106,X107)|~m1_subset_1(X108,k1_zfmisc_1(k2_zfmisc_1(X106,X107)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.47/0.63  cnf(c_0_84, negated_conjecture, (k2_relat_1(k7_relat_1(esk5_0,X1))=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_66, c_0_47])).
% 0.47/0.63  cnf(c_0_85, negated_conjecture, (k7_relat_1(esk5_0,esk4_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_47])])).
% 0.47/0.63  cnf(c_0_86, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.47/0.63  cnf(c_0_87, plain, (k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.47/0.63  fof(c_0_88, plain, ![X41, X42, X43]:(~r2_hidden(X41,X42)|~m1_subset_1(X42,k1_zfmisc_1(X43))|~v1_xboole_0(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.47/0.63  fof(c_0_89, plain, ![X20, X21]:((r2_hidden(esk3_2(X20,X21),X21)|~r2_xboole_0(X20,X21))&(~r2_hidden(esk3_2(X20,X21),X20)|~r2_xboole_0(X20,X21))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 0.47/0.63  cnf(c_0_90, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.47/0.63  cnf(c_0_91, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.47/0.63  cnf(c_0_92, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_partfun1(esk4_0))|~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_partfun1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.63  cnf(c_0_93, negated_conjecture, (k1_partfun1(X1,X2,esk4_0,esk4_0,X3,esk5_0)=k5_relat_1(X3,esk5_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_38]), c_0_37])])).
% 0.47/0.63  cnf(c_0_94, negated_conjecture, (m1_subset_1(k2_funct_2(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_62]), c_0_36]), c_0_37]), c_0_38])])).
% 0.47/0.63  cnf(c_0_95, negated_conjecture, (k5_relat_1(k2_funct_2(esk4_0,esk5_0),esk5_0)=k6_relat_1(esk4_0)), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 0.47/0.63  cnf(c_0_96, negated_conjecture, (v1_funct_1(k2_funct_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_62]), c_0_36]), c_0_37]), c_0_38])])).
% 0.47/0.63  cnf(c_0_97, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_79])).
% 0.47/0.63  cnf(c_0_98, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.47/0.63  cnf(c_0_99, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_46]), c_0_37]), c_0_47])])).
% 0.47/0.63  cnf(c_0_100, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.47/0.63  cnf(c_0_101, negated_conjecture, (k9_relat_1(esk5_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_60])).
% 0.47/0.63  cnf(c_0_102, negated_conjecture, (k9_relat_1(esk5_0,X1)=k7_relset_1(esk4_0,esk4_0,esk5_0,X1)), inference(spm,[status(thm)],[c_0_86, c_0_38])).
% 0.47/0.63  cnf(c_0_103, negated_conjecture, (k7_relset_1(esk4_0,esk4_0,esk5_0,esk4_0)=k2_relset_1(esk4_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_87, c_0_38])).
% 0.47/0.63  fof(c_0_104, plain, ![X49]:(v1_xboole_0(X49)|~v1_relat_1(X49)|~v1_xboole_0(k2_relat_1(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).
% 0.47/0.63  fof(c_0_105, plain, ![X57]:(k1_relat_1(k6_relat_1(X57))=X57&k2_relat_1(k6_relat_1(X57))=X57), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.47/0.63  fof(c_0_106, plain, ![X58]:(v1_relat_1(k6_relat_1(X58))&v1_funct_1(k6_relat_1(X58))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.47/0.63  cnf(c_0_107, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.47/0.63  cnf(c_0_108, plain, (r2_hidden(esk3_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.47/0.63  cnf(c_0_109, plain, (k1_xboole_0=X1|r2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.47/0.63  cnf(c_0_110, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_relat_1(esk4_0))|~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_relat_1(esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_81]), c_0_81])).
% 0.47/0.63  cnf(c_0_111, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0)=k6_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_96])])).
% 0.47/0.63  cnf(c_0_112, plain, (r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.47/0.63  cnf(c_0_113, negated_conjecture, (k1_partfun1(X1,X2,esk4_0,esk4_0,X3,k2_funct_2(esk4_0,esk5_0))=k5_relat_1(X3,k2_funct_2(esk4_0,esk5_0))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_94]), c_0_96])])).
% 0.47/0.63  cnf(c_0_114, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_2(esk4_0,esk5_0))=k6_relat_1(k1_relat_1(esk5_0))), inference(rw,[status(thm)],[c_0_99, c_0_77])).
% 0.47/0.63  cnf(c_0_115, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_100, c_0_81])).
% 0.47/0.63  cnf(c_0_116, negated_conjecture, (k2_relset_1(esk4_0,esk4_0,esk5_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102]), c_0_103])).
% 0.47/0.63  fof(c_0_117, plain, ![X19]:(~v1_xboole_0(X19)|X19=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.47/0.63  cnf(c_0_118, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.47/0.63  cnf(c_0_119, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.47/0.63  cnf(c_0_120, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.47/0.63  cnf(c_0_121, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_107, c_0_38])).
% 0.47/0.63  cnf(c_0_122, plain, (k1_xboole_0=X1|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.47/0.63  fof(c_0_123, plain, ![X32, X33]:(~v1_xboole_0(X33)|v1_xboole_0(k2_zfmisc_1(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.47/0.63  cnf(c_0_124, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111]), c_0_112])])).
% 0.47/0.63  cnf(c_0_125, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0))=k6_relat_1(k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_38]), c_0_114]), c_0_37])])).
% 0.47/0.63  cnf(c_0_126, negated_conjecture, (k6_relat_1(k1_relat_1(esk5_0))=k6_relat_1(esk4_0)|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_77]), c_0_114]), c_0_62]), c_0_46]), c_0_37]), c_0_38])])).
% 0.47/0.63  cnf(c_0_127, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.47/0.63  cnf(c_0_128, plain, (v1_xboole_0(k6_relat_1(X1))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120])])).
% 0.47/0.63  fof(c_0_129, plain, ![X39, X40]:((~m1_subset_1(X39,k1_zfmisc_1(X40))|r1_tarski(X39,X40))&(~r1_tarski(X39,X40)|m1_subset_1(X39,k1_zfmisc_1(X40)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.47/0.63  cnf(c_0_130, negated_conjecture, (esk5_0=k1_xboole_0|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 0.47/0.63  cnf(c_0_131, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.47/0.63  cnf(c_0_132, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,k6_relat_1(k1_relat_1(esk5_0)),k6_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_124, c_0_125])).
% 0.47/0.63  cnf(c_0_133, negated_conjecture, (k1_relat_1(esk5_0)=esk4_0|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_126]), c_0_119])).
% 0.47/0.63  cnf(c_0_134, plain, (k6_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 0.47/0.63  cnf(c_0_135, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.47/0.63  cnf(c_0_136, negated_conjecture, (esk5_0=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 0.47/0.63  cnf(c_0_137, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_112])])).
% 0.47/0.63  cnf(c_0_138, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.47/0.63  cnf(c_0_139, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_134, c_0_73])).
% 0.47/0.63  cnf(c_0_140, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_135, c_0_91])).
% 0.47/0.63  cnf(c_0_141, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136, c_0_137]), c_0_73])])).
% 0.47/0.63  cnf(c_0_142, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 0.47/0.63  cnf(c_0_143, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_97, c_0_140])).
% 0.47/0.63  cnf(c_0_144, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_137]), c_0_137]), c_0_137]), c_0_139]), c_0_141]), c_0_142]), c_0_139]), c_0_143])]), ['proof']).
% 0.47/0.63  # SZS output end CNFRefutation
% 0.47/0.63  # Proof object total steps             : 145
% 0.47/0.63  # Proof object clause steps            : 87
% 0.47/0.63  # Proof object formula steps           : 58
% 0.47/0.63  # Proof object conjectures             : 43
% 0.47/0.63  # Proof object clause conjectures      : 40
% 0.47/0.63  # Proof object formula conjectures     : 3
% 0.47/0.63  # Proof object initial clauses used    : 38
% 0.47/0.63  # Proof object initial formulas used   : 29
% 0.47/0.63  # Proof object generating inferences   : 37
% 0.47/0.63  # Proof object simplifying inferences  : 78
% 0.47/0.63  # Training examples: 0 positive, 0 negative
% 0.47/0.63  # Parsed axioms                        : 48
% 0.47/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.63  # Initial clauses                      : 85
% 0.47/0.63  # Removed in clause preprocessing      : 2
% 0.47/0.63  # Initial clauses in saturation        : 83
% 0.47/0.63  # Processed clauses                    : 3009
% 0.47/0.63  # ...of these trivial                  : 69
% 0.47/0.63  # ...subsumed                          : 842
% 0.47/0.63  # ...remaining for further processing  : 2097
% 0.47/0.63  # Other redundant clauses eliminated   : 12
% 0.47/0.63  # Clauses deleted for lack of memory   : 0
% 0.47/0.63  # Backward-subsumed                    : 8
% 0.47/0.63  # Backward-rewritten                   : 717
% 0.47/0.63  # Generated clauses                    : 12214
% 0.47/0.63  # ...of the previous two non-trivial   : 11264
% 0.47/0.63  # Contextual simplify-reflections      : 4
% 0.47/0.63  # Paramodulations                      : 12203
% 0.47/0.63  # Factorizations                       : 0
% 0.47/0.63  # Equation resolutions                 : 12
% 0.47/0.63  # Propositional unsat checks           : 0
% 0.47/0.63  #    Propositional check models        : 0
% 0.47/0.63  #    Propositional check unsatisfiable : 0
% 0.47/0.63  #    Propositional clauses             : 0
% 0.47/0.63  #    Propositional clauses after purity: 0
% 0.47/0.63  #    Propositional unsat core size     : 0
% 0.47/0.63  #    Propositional preprocessing time  : 0.000
% 0.47/0.63  #    Propositional encoding time       : 0.000
% 0.47/0.63  #    Propositional solver time         : 0.000
% 0.47/0.63  #    Success case prop preproc time    : 0.000
% 0.47/0.63  #    Success case prop encoding time   : 0.000
% 0.47/0.63  #    Success case prop solver time     : 0.000
% 0.47/0.63  # Current number of processed clauses  : 1282
% 0.47/0.63  #    Positive orientable unit clauses  : 90
% 0.47/0.63  #    Positive unorientable unit clauses: 2
% 0.47/0.63  #    Negative unit clauses             : 2
% 0.47/0.63  #    Non-unit-clauses                  : 1188
% 0.47/0.63  # Current number of unprocessed clauses: 8377
% 0.47/0.63  # ...number of literals in the above   : 17049
% 0.47/0.63  # Current number of archived formulas  : 0
% 0.47/0.63  # Current number of archived clauses   : 807
% 0.47/0.63  # Clause-clause subsumption calls (NU) : 359669
% 0.47/0.63  # Rec. Clause-clause subsumption calls : 312570
% 0.47/0.63  # Non-unit clause-clause subsumptions  : 840
% 0.47/0.63  # Unit Clause-clause subsumption calls : 6767
% 0.47/0.63  # Rewrite failures with RHS unbound    : 0
% 0.47/0.63  # BW rewrite match attempts            : 1041
% 0.47/0.63  # BW rewrite match successes           : 48
% 0.47/0.63  # Condensation attempts                : 0
% 0.47/0.63  # Condensation successes               : 0
% 0.47/0.63  # Termbank termtop insertions          : 194428
% 0.47/0.63  
% 0.47/0.63  # -------------------------------------------------
% 0.47/0.63  # User time                : 0.279 s
% 0.47/0.63  # System time              : 0.014 s
% 0.47/0.63  # Total time               : 0.293 s
% 0.47/0.63  # Maximum resident set size: 1636 pages
%------------------------------------------------------------------------------
