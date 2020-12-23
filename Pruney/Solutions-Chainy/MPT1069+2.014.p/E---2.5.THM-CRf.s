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
% DateTime   : Thu Dec  3 11:07:51 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 606 expanded)
%              Number of clauses        :   64 ( 235 expanded)
%              Number of leaves         :   18 ( 144 expanded)
%              Depth                    :   13
%              Number of atoms          :  372 (3603 expanded)
%              Number of equality atoms :   94 ( 760 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t186_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t185_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k1_funct_1(X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
           => ! [X5] :
                ( ( v1_funct_1(X5)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                     => ( X2 = k1_xboole_0
                        | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t186_funct_2])).

fof(c_0_19,plain,(
    ! [X64,X65,X66,X67] :
      ( ( v1_funct_1(X67)
        | X65 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X64,X65,X67),X66)
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X64,X65)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( v1_funct_2(X67,X64,X66)
        | X65 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X64,X65,X67),X66)
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X64,X65)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X66)))
        | X65 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X64,X65,X67),X66)
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X64,X65)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( v1_funct_1(X67)
        | X64 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X64,X65,X67),X66)
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X64,X65)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( v1_funct_2(X67,X64,X66)
        | X64 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X64,X65,X67),X66)
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X64,X65)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X66)))
        | X64 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X64,X65,X67),X66)
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X64,X65)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk6_0,esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
    & v1_funct_1(esk9_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))
    & m1_subset_1(esk10_0,esk6_0)
    & r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0))
    & esk6_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0) != k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_21,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k1_relset_1(X45,X46,X47) = k1_relat_1(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X54,X55,X56,X57,X58,X59] :
      ( v1_xboole_0(X56)
      | ~ v1_funct_1(X57)
      | ~ v1_funct_2(X57,X55,X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
      | ~ v1_funct_1(X58)
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X54)))
      | ~ m1_subset_1(X59,X55)
      | ~ r1_tarski(k2_relset_1(X55,X56,X57),k1_relset_1(X56,X54,X58))
      | X55 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X55,X56,X54,X57,X58),X59) = k1_funct_1(X58,k1_funct_1(X57,X59)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

fof(c_0_30,plain,(
    ! [X42,X43,X44] :
      ( ( v4_relat_1(X44,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( v5_relat_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_31,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_relset_1(esk7_0,esk5_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( k1_relset_1(esk7_0,esk5_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | v1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | X3 = k1_xboole_0
    | k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6) = k1_funct_1(X4,k1_funct_1(X2,X6))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ m1_subset_1(X6,X3)
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_37,plain,(
    ! [X20,X21] :
      ( ( ~ v5_relat_1(X21,X20)
        | r1_tarski(k2_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_tarski(k2_relat_1(X21),X20)
        | v5_relat_1(X21,X20)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_38,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_relat_1(esk9_0)))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_41,plain,(
    ! [X48,X49,X50] :
      ( ( ~ v1_funct_2(X50,X48,X49)
        | X48 = k1_relset_1(X48,X49,X50)
        | X49 = k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X48 != k1_relset_1(X48,X49,X50)
        | v1_funct_2(X50,X48,X49)
        | X49 = k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( ~ v1_funct_2(X50,X48,X49)
        | X48 = k1_relset_1(X48,X49,X50)
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X48 != k1_relset_1(X48,X49,X50)
        | v1_funct_2(X50,X48,X49)
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( ~ v1_funct_2(X50,X48,X49)
        | X50 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X50 != k1_xboole_0
        | v1_funct_2(X50,X48,X49)
        | X48 = k1_xboole_0
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_42,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_43,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X13,X14)
      | v1_xboole_0(X14)
      | r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk7_0,esk5_0,X2,esk9_0),X3) = k1_funct_1(esk9_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk7_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk7_0,X2),k1_relset_1(esk7_0,esk5_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_35])]),c_0_36])).

fof(c_0_45,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | v5_relat_1(esk8_0,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_26])).

cnf(c_0_49,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X60,X61,X62,X63] :
      ( ~ v1_funct_1(X63)
      | ~ v1_funct_2(X63,X60,X61)
      | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | ~ r2_hidden(X62,X60)
      | X61 = k1_xboole_0
      | r2_hidden(k1_funct_1(X63,X62),X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_51,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | v1_funct_2(esk8_0,esk6_0,X1)
    | ~ r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_24]),c_0_25])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_32])).

fof(c_0_53,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk10_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk7_0,esk5_0,X2,esk9_0),X3) = k1_funct_1(esk9_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk7_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk7_0,X2),k1_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_58,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(k2_relat_1(esk8_0),k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

fof(c_0_61,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ v1_funct_1(X36)
      | ~ r2_hidden(X35,k1_relat_1(X36))
      | r2_hidden(k1_funct_1(X36,X35),k2_relat_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_62,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk8_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_26]),c_0_24])])).

cnf(c_0_63,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_64,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | v1_funct_2(esk8_0,esk6_0,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0)
    | v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),X1) = k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1))
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_24]),c_0_25]),c_0_26])]),c_0_57])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | m1_subset_1(k2_relat_1(esk8_0),k1_zfmisc_1(k1_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_71,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_72,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_74,plain,(
    ! [X51,X52,X53] :
      ( ~ v1_relat_1(X52)
      | ~ v5_relat_1(X52,X51)
      | ~ v1_funct_1(X52)
      | ~ r2_hidden(X53,k1_relat_1(X52))
      | k7_partfun1(X51,X52,X53) = k1_funct_1(X52,X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_75,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk8_0,X1),k1_relat_1(esk9_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_39]),c_0_25])]),c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_57])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),X1) = k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1))
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_52])])).

cnf(c_0_78,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk8_0))
    | ~ v1_xboole_0(k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk8_0,X1),k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_25]),c_0_48])])).

cnf(c_0_81,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk8_0,esk10_0),k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_28])).

cnf(c_0_84,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0) != k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0) = k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_55])).

fof(c_0_86,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | ~ r1_tarski(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_87,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_88,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_1(k1_relat_1(esk9_0)),k1_relat_1(esk9_0))
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk8_0,esk10_0),k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_76])).

cnf(c_0_90,negated_conjecture,
    ( k7_partfun1(X1,esk9_0,k1_funct_1(esk8_0,esk10_0)) = k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))
    | k1_relat_1(esk9_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | ~ v5_relat_1(esk9_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_35]),c_0_83])])).

cnf(c_0_91,negated_conjecture,
    ( v5_relat_1(esk9_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_92,negated_conjecture,
    ( k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)) != k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_93,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_94,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_1(k1_relat_1(esk9_0)),k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])).

cnf(c_0_97,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_79])).

cnf(c_0_99,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99]),c_0_99]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:31:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.19/0.40  # and selection function SelectNewComplexAHP.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 0.19/0.40  fof(t8_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 0.19/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.40  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 0.19/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.40  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.40  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.19/0.41  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.41  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.41  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 0.19/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.41  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.19/0.41  fof(c_0_19, plain, ![X64, X65, X66, X67]:((((v1_funct_1(X67)|X65=k1_xboole_0|~r1_tarski(k2_relset_1(X64,X65,X67),X66)|(~v1_funct_1(X67)|~v1_funct_2(X67,X64,X65)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))&(v1_funct_2(X67,X64,X66)|X65=k1_xboole_0|~r1_tarski(k2_relset_1(X64,X65,X67),X66)|(~v1_funct_1(X67)|~v1_funct_2(X67,X64,X65)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))))&(m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X66)))|X65=k1_xboole_0|~r1_tarski(k2_relset_1(X64,X65,X67),X66)|(~v1_funct_1(X67)|~v1_funct_2(X67,X64,X65)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))))&(((v1_funct_1(X67)|X64!=k1_xboole_0|~r1_tarski(k2_relset_1(X64,X65,X67),X66)|(~v1_funct_1(X67)|~v1_funct_2(X67,X64,X65)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))&(v1_funct_2(X67,X64,X66)|X64!=k1_xboole_0|~r1_tarski(k2_relset_1(X64,X65,X67),X66)|(~v1_funct_1(X67)|~v1_funct_2(X67,X64,X65)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))))&(m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X66)))|X64!=k1_xboole_0|~r1_tarski(k2_relset_1(X64,X65,X67),X66)|(~v1_funct_1(X67)|~v1_funct_2(X67,X64,X65)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).
% 0.19/0.41  fof(c_0_20, negated_conjecture, (~v1_xboole_0(esk7_0)&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&((v1_funct_1(esk9_0)&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0))))&(m1_subset_1(esk10_0,esk6_0)&(r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0))&(esk6_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0)!=k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.19/0.41  fof(c_0_21, plain, ![X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k1_relset_1(X45,X46,X47)=k1_relat_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.41  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_27, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  fof(c_0_29, plain, ![X54, X55, X56, X57, X58, X59]:(v1_xboole_0(X56)|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))|(~v1_funct_1(X58)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X54)))|(~m1_subset_1(X59,X55)|(~r1_tarski(k2_relset_1(X55,X56,X57),k1_relset_1(X56,X54,X58))|(X55=k1_xboole_0|k1_funct_1(k8_funct_2(X55,X56,X54,X57,X58),X59)=k1_funct_1(X58,k1_funct_1(X57,X59)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.19/0.41  fof(c_0_30, plain, ![X42, X43, X44]:((v4_relat_1(X44,X42)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(v5_relat_1(X44,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (esk7_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_relset_1(esk7_0,esk5_0,esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (k1_relset_1(esk7_0,esk5_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.41  fof(c_0_33, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.41  cnf(c_0_34, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  fof(c_0_37, plain, ![X20, X21]:((~v5_relat_1(X21,X20)|r1_tarski(k2_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_tarski(k2_relat_1(X21),X20)|v5_relat_1(X21,X20)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.41  cnf(c_0_38, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (esk7_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_relat_1(esk9_0))))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.41  cnf(c_0_40, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  fof(c_0_41, plain, ![X48, X49, X50]:((((~v1_funct_2(X50,X48,X49)|X48=k1_relset_1(X48,X49,X50)|X49=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X48!=k1_relset_1(X48,X49,X50)|v1_funct_2(X50,X48,X49)|X49=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))&((~v1_funct_2(X50,X48,X49)|X48=k1_relset_1(X48,X49,X50)|X48!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X48!=k1_relset_1(X48,X49,X50)|v1_funct_2(X50,X48,X49)|X48!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))))&((~v1_funct_2(X50,X48,X49)|X50=k1_xboole_0|X48=k1_xboole_0|X49!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X50!=k1_xboole_0|v1_funct_2(X50,X48,X49)|X48=k1_xboole_0|X49!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.41  cnf(c_0_42, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  fof(c_0_43, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk7_0,esk5_0,X2,esk9_0),X3)=k1_funct_1(esk9_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk7_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk7_0,X2),k1_relset_1(esk7_0,esk5_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_35])]), c_0_36])).
% 0.19/0.41  fof(c_0_45, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.41  cnf(c_0_46, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (esk7_0=k1_xboole_0|v5_relat_1(esk8_0,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_40, c_0_26])).
% 0.19/0.41  cnf(c_0_49, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.41  fof(c_0_50, plain, ![X60, X61, X62, X63]:(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(~r2_hidden(X62,X60)|(X61=k1_xboole_0|r2_hidden(k1_funct_1(X63,X62),X61)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (esk7_0=k1_xboole_0|v1_funct_2(esk8_0,esk6_0,X1)|~r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_24]), c_0_25])])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relat_1(esk9_0))), inference(rw,[status(thm)],[c_0_23, c_0_32])).
% 0.19/0.41  fof(c_0_53, plain, ![X11]:(~v1_xboole_0(X11)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.41  cnf(c_0_54, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk10_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk7_0,esk5_0,X2,esk9_0),X3)=k1_funct_1(esk9_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk7_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk7_0,X2),k1_relat_1(esk9_0))), inference(rw,[status(thm)],[c_0_44, c_0_32])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  fof(c_0_58, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.41  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(k2_relat_1(esk8_0),k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.19/0.41  fof(c_0_61, plain, ![X35, X36]:(~v1_relat_1(X36)|~v1_funct_1(X36)|(~r2_hidden(X35,k1_relat_1(X36))|r2_hidden(k1_funct_1(X36,X35),k2_relat_1(X36)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk8_0)=esk6_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_26]), c_0_24])])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.19/0.41  cnf(c_0_64, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (esk7_0=k1_xboole_0|v1_funct_2(esk8_0,esk6_0,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.41  cnf(c_0_66, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (r2_hidden(esk10_0,esk6_0)|v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),X1)=k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1))|~m1_subset_1(X1,esk6_0)|~r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_24]), c_0_25]), c_0_26])]), c_0_57])).
% 0.19/0.41  cnf(c_0_69, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (esk7_0=k1_xboole_0|m1_subset_1(k2_relat_1(esk8_0),k1_zfmisc_1(k1_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.41  fof(c_0_71, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_72, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.41  fof(c_0_74, plain, ![X51, X52, X53]:(~v1_relat_1(X52)|~v5_relat_1(X52,X51)|~v1_funct_1(X52)|(~r2_hidden(X53,k1_relat_1(X52))|k7_partfun1(X51,X52,X53)=k1_funct_1(X52,X53))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.19/0.41  cnf(c_0_75, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(k1_funct_1(esk8_0,X1),k1_relat_1(esk9_0))|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_39]), c_0_25])]), c_0_65])).
% 0.19/0.41  cnf(c_0_76, negated_conjecture, (r2_hidden(esk10_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_57])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, (k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),X1)=k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1))|~m1_subset_1(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_52])])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (esk7_0=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk8_0))|~v1_xboole_0(k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.41  cnf(c_0_79, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.41  cnf(c_0_80, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(k1_funct_1(esk8_0,X1),k2_relat_1(esk8_0))|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_25]), c_0_48])])).
% 0.19/0.41  cnf(c_0_81, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(k1_funct_1(esk8_0,esk10_0),k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.41  cnf(c_0_83, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_40, c_0_28])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, (k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0)!=k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_85, negated_conjecture, (k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0)=k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))), inference(spm,[status(thm)],[c_0_77, c_0_55])).
% 0.19/0.41  fof(c_0_86, plain, ![X37, X38]:(~r2_hidden(X37,X38)|~r1_tarski(X38,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.41  fof(c_0_87, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.41  cnf(c_0_88, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_1(k1_relat_1(esk9_0)),k1_relat_1(esk9_0))|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.41  cnf(c_0_89, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(k1_funct_1(esk8_0,esk10_0),k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_80, c_0_76])).
% 0.19/0.41  cnf(c_0_90, negated_conjecture, (k7_partfun1(X1,esk9_0,k1_funct_1(esk8_0,esk10_0))=k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))|k1_relat_1(esk9_0)=k1_xboole_0|esk7_0=k1_xboole_0|~v5_relat_1(esk9_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_35]), c_0_83])])).
% 0.19/0.41  cnf(c_0_91, negated_conjecture, (v5_relat_1(esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_28])).
% 0.19/0.41  cnf(c_0_92, negated_conjecture, (k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0))!=k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))), inference(rw,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.41  cnf(c_0_93, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.41  cnf(c_0_94, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.41  cnf(c_0_95, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_1(k1_relat_1(esk9_0)),k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.41  cnf(c_0_96, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])).
% 0.19/0.41  cnf(c_0_97, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.19/0.41  cnf(c_0_98, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_36, c_0_79])).
% 0.19/0.41  cnf(c_0_99, negated_conjecture, (esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])).
% 0.19/0.41  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99]), c_0_99]), c_0_97]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 101
% 0.19/0.41  # Proof object clause steps            : 64
% 0.19/0.41  # Proof object formula steps           : 37
% 0.19/0.41  # Proof object conjectures             : 48
% 0.19/0.41  # Proof object clause conjectures      : 45
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 28
% 0.19/0.41  # Proof object initial formulas used   : 18
% 0.19/0.41  # Proof object generating inferences   : 30
% 0.19/0.41  # Proof object simplifying inferences  : 39
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 21
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 51
% 0.19/0.41  # Removed in clause preprocessing      : 2
% 0.19/0.41  # Initial clauses in saturation        : 49
% 0.19/0.41  # Processed clauses                    : 489
% 0.19/0.41  # ...of these trivial                  : 3
% 0.19/0.41  # ...subsumed                          : 129
% 0.19/0.41  # ...remaining for further processing  : 357
% 0.19/0.41  # Other redundant clauses eliminated   : 13
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 16
% 0.19/0.41  # Backward-rewritten                   : 166
% 0.19/0.41  # Generated clauses                    : 947
% 0.19/0.41  # ...of the previous two non-trivial   : 1000
% 0.19/0.41  # Contextual simplify-reflections      : 3
% 0.19/0.41  # Paramodulations                      : 936
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 13
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 116
% 0.19/0.41  #    Positive orientable unit clauses  : 24
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 5
% 0.19/0.41  #    Non-unit-clauses                  : 87
% 0.19/0.41  # Current number of unprocessed clauses: 517
% 0.19/0.41  # ...number of literals in the above   : 2054
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 231
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 8153
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 4012
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 120
% 0.19/0.41  # Unit Clause-clause subsumption calls : 439
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 26
% 0.19/0.41  # BW rewrite match successes           : 18
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 19831
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.064 s
% 0.19/0.41  # System time              : 0.009 s
% 0.19/0.41  # Total time               : 0.072 s
% 0.19/0.41  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
