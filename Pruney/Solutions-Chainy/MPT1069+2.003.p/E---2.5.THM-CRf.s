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
% DateTime   : Thu Dec  3 11:07:49 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 372 expanded)
%              Number of clauses        :   66 ( 148 expanded)
%              Number of leaves         :   20 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  366 (1996 expanded)
%              Number of equality atoms :   73 ( 407 expanded)
%              Maximal formula depth    :   16 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc4_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(cc6_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & ~ v1_xboole_0(X3)
              & v1_funct_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_20,negated_conjecture,(
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

fof(c_0_21,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k1_relset_1(X43,X44,X45) = k1_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v1_funct_1(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))
    & m1_subset_1(esk7_0,esk3_0)
    & r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),k1_relset_1(esk4_0,esk2_0,esk6_0))
    & esk3_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk3_0,esk4_0,esk2_0,esk5_0,esk6_0),esk7_0) != k7_partfun1(esk2_0,esk6_0,k1_funct_1(esk5_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_23,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X65,X66,X67,X68] :
      ( ( v1_funct_1(X68)
        | X66 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X65,X66,X68),X67)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( v1_funct_2(X68,X65,X67)
        | X66 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X65,X66,X68),X67)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X67)))
        | X66 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X65,X66,X68),X67)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( v1_funct_1(X68)
        | X65 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X65,X66,X68),X67)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( v1_funct_2(X68,X65,X67)
        | X65 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X65,X66,X68),X67)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X67)))
        | X65 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X65,X66,X68),X67)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X65,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).

fof(c_0_27,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),k1_relset_1(esk4_0,esk2_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k1_relset_1(esk4_0,esk2_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_35,plain,(
    ! [X55,X56,X57,X58,X59,X60] :
      ( v1_xboole_0(X57)
      | ~ v1_funct_1(X58)
      | ~ v1_funct_2(X58,X56,X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | ~ v1_funct_1(X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X55)))
      | ~ m1_subset_1(X60,X56)
      | ~ r1_tarski(k2_relset_1(X56,X57,X58),k1_relset_1(X57,X55,X59))
      | X56 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X56,X57,X55,X58,X59),X60) = k1_funct_1(X59,k1_funct_1(X58,X60)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

fof(c_0_36,plain,(
    ! [X40,X41,X42] :
      ( ( v4_relat_1(X42,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( v5_relat_1(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

fof(c_0_39,plain,(
    ! [X61,X62,X63,X64] :
      ( ~ v1_funct_1(X64)
      | ~ v1_funct_2(X64,X61,X62)
      | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
      | ~ r2_hidden(X63,X61)
      | X62 = k1_xboole_0
      | r2_hidden(k1_funct_1(X64,X63),X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),k1_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk5_0,esk3_0,X1)
    | ~ r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

fof(c_0_43,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_47,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_48,plain,(
    ! [X26,X27] :
      ( ( ~ v5_relat_1(X27,X26)
        | r1_tarski(k2_relat_1(X27),X26)
        | ~ v1_relat_1(X27) )
      & ( ~ r1_tarski(k2_relat_1(X27),X26)
        | v5_relat_1(X27,X26)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_49,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_51,plain,(
    ! [X28,X29] : v1_relat_1(k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_52,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33]),c_0_34]),c_0_32])])).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk5_0,esk3_0,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk7_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_57,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | v1_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk4_0,esk2_0,X2,esk6_0),X3) = k1_funct_1(esk6_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk4_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk4_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk4_0,X2),k1_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_45]),c_0_30])]),c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( v5_relat_1(k2_zfmisc_1(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_64,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_65,plain,(
    ! [X52,X53,X54] :
      ( ~ v1_relat_1(X53)
      | ~ v5_relat_1(X53,X52)
      | ~ v1_funct_1(X53)
      | ~ r2_hidden(X54,k1_relat_1(X53))
      | k7_partfun1(X52,X53,X54) = k1_funct_1(X53,X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk5_0,X1),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_34])]),c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk7_0,esk3_0)
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk3_0,esk4_0,esk2_0,esk5_0,esk6_0),X1) = k1_funct_1(esk6_0,k1_funct_1(esk5_0,X1))
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_33]),c_0_34]),c_0_32]),c_0_41])]),c_0_59])).

fof(c_0_70,plain,(
    ! [X30] :
      ( v1_xboole_0(X30)
      | ~ v1_relat_1(X30)
      | ~ v1_xboole_0(k2_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_74,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_75,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | v1_xboole_0(k2_zfmisc_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).

fof(c_0_76,plain,(
    ! [X49,X50,X51] :
      ( ( v1_funct_1(X51)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | v1_xboole_0(X49)
        | v1_xboole_0(X50) )
      & ( ~ v1_xboole_0(X51)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | v1_xboole_0(X49)
        | v1_xboole_0(X50) )
      & ( v1_funct_2(X51,X49,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | v1_xboole_0(X49)
        | v1_xboole_0(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

fof(c_0_77,plain,(
    ! [X34] :
      ( ~ v1_xboole_0(X34)
      | v1_funct_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_78,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk5_0,esk7_0),k1_relat_1(esk6_0))
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_25])).

cnf(c_0_81,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk3_0,esk4_0,esk2_0,esk5_0,esk6_0),esk7_0) != k7_partfun1(esk2_0,esk6_0,k1_funct_1(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_82,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk3_0,esk4_0,esk2_0,esk5_0,esk6_0),esk7_0) = k1_funct_1(esk6_0,k1_funct_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_56])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_84,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_85,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_86,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,k1_relat_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_53])).

cnf(c_0_87,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_88,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_89,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_90,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_91,negated_conjecture,
    ( k7_partfun1(X1,esk6_0,k1_funct_1(esk5_0,esk7_0)) = k1_funct_1(esk6_0,k1_funct_1(esk5_0,esk7_0))
    | k1_relat_1(esk6_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | v1_xboole_0(esk3_0)
    | ~ v5_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_45]),c_0_80])])).

cnf(c_0_92,negated_conjecture,
    ( v5_relat_1(esk6_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_25])).

cnf(c_0_93,negated_conjecture,
    ( k7_partfun1(esk2_0,esk6_0,k1_funct_1(esk5_0,esk7_0)) != k1_funct_1(esk6_0,k1_funct_1(esk5_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_94,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_64]),c_0_85])])).

cnf(c_0_95,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k1_relat_1(esk6_0)) = esk5_0
    | esk4_0 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,k1_relat_1(esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_86])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_97,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_99,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_61])])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_32]),c_0_33])]),c_0_46])).

cnf(c_0_102,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_98]),c_0_99]),c_0_99]),c_0_61])]),c_0_100])).

cnf(c_0_103,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_85])])).

cnf(c_0_104,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_103]),c_0_59])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_104]),c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.20/0.47  # and selection function SelectNewComplexAHP.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.029 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 0.20/0.47  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.47  fof(t8_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 0.20/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.47  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 0.20/0.47  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.47  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 0.20/0.47  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.47  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.47  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.47  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.47  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.47  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 0.20/0.47  fof(fc9_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 0.20/0.47  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.47  fof(fc4_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 0.20/0.47  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.20/0.47  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.20/0.47  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.47  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.20/0.47  fof(c_0_21, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k1_relset_1(X43,X44,X45)=k1_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.47  fof(c_0_22, negated_conjecture, (~v1_xboole_0(esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((v1_funct_1(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))))&(m1_subset_1(esk7_0,esk3_0)&(r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),k1_relset_1(esk4_0,esk2_0,esk6_0))&(esk3_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk3_0,esk4_0,esk2_0,esk5_0,esk6_0),esk7_0)!=k7_partfun1(esk2_0,esk6_0,k1_funct_1(esk5_0,esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.20/0.47  fof(c_0_23, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.47  cnf(c_0_24, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  fof(c_0_26, plain, ![X65, X66, X67, X68]:((((v1_funct_1(X68)|X66=k1_xboole_0|~r1_tarski(k2_relset_1(X65,X66,X68),X67)|(~v1_funct_1(X68)|~v1_funct_2(X68,X65,X66)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))))&(v1_funct_2(X68,X65,X67)|X66=k1_xboole_0|~r1_tarski(k2_relset_1(X65,X66,X68),X67)|(~v1_funct_1(X68)|~v1_funct_2(X68,X65,X66)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))))&(m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X67)))|X66=k1_xboole_0|~r1_tarski(k2_relset_1(X65,X66,X68),X67)|(~v1_funct_1(X68)|~v1_funct_2(X68,X65,X66)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))))&(((v1_funct_1(X68)|X65!=k1_xboole_0|~r1_tarski(k2_relset_1(X65,X66,X68),X67)|(~v1_funct_1(X68)|~v1_funct_2(X68,X65,X66)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))))&(v1_funct_2(X68,X65,X67)|X65!=k1_xboole_0|~r1_tarski(k2_relset_1(X65,X66,X68),X67)|(~v1_funct_1(X68)|~v1_funct_2(X68,X65,X66)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))))&(m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X67)))|X65!=k1_xboole_0|~r1_tarski(k2_relset_1(X65,X66,X68),X67)|(~v1_funct_1(X68)|~v1_funct_2(X68,X65,X66)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).
% 0.20/0.47  fof(c_0_27, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.47  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_29, negated_conjecture, (r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),k1_relset_1(esk4_0,esk2_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_30, negated_conjecture, (k1_relset_1(esk4_0,esk2_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.47  cnf(c_0_31, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  fof(c_0_35, plain, ![X55, X56, X57, X58, X59, X60]:(v1_xboole_0(X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|(~v1_funct_1(X59)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X55)))|(~m1_subset_1(X60,X56)|(~r1_tarski(k2_relset_1(X56,X57,X58),k1_relset_1(X57,X55,X59))|(X56=k1_xboole_0|k1_funct_1(k8_funct_2(X56,X57,X55,X58,X59),X60)=k1_funct_1(X59,k1_funct_1(X58,X60)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.20/0.47  fof(c_0_36, plain, ![X40, X41, X42]:((v4_relat_1(X42,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(v5_relat_1(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.47  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.47  fof(c_0_39, plain, ![X61, X62, X63, X64]:(~v1_funct_1(X64)|~v1_funct_2(X64,X61,X62)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))|(~r2_hidden(X63,X61)|(X62=k1_xboole_0|r2_hidden(k1_funct_1(X64,X63),X62)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.20/0.47  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_41, negated_conjecture, (r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),k1_relat_1(esk6_0))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.47  cnf(c_0_42, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk5_0,esk3_0,X1)|~r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.20/0.47  fof(c_0_43, plain, ![X17, X18]:(~m1_subset_1(X17,X18)|(v1_xboole_0(X18)|r2_hidden(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.47  cnf(c_0_44, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.47  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  fof(c_0_47, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.47  fof(c_0_48, plain, ![X26, X27]:((~v5_relat_1(X27,X26)|r1_tarski(k2_relat_1(X27),X26)|~v1_relat_1(X27))&(~r1_tarski(k2_relat_1(X27),X26)|v5_relat_1(X27,X26)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.47  cnf(c_0_49, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.47  fof(c_0_51, plain, ![X28, X29]:v1_relat_1(k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.47  cnf(c_0_52, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.47  cnf(c_0_53, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_33]), c_0_34]), c_0_32])])).
% 0.20/0.47  cnf(c_0_54, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk5_0,esk3_0,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 0.20/0.47  cnf(c_0_55, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.47  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk7_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  fof(c_0_57, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|v1_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.47  cnf(c_0_58, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk4_0,esk2_0,X2,esk6_0),X3)=k1_funct_1(esk6_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk4_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk4_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk4_0,X2),k1_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_25]), c_0_45]), c_0_30])]), c_0_46])).
% 0.20/0.47  cnf(c_0_59, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_60, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_61, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.47  cnf(c_0_62, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.47  cnf(c_0_63, plain, (v5_relat_1(k2_zfmisc_1(X1,X2),X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.47  cnf(c_0_64, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.47  fof(c_0_65, plain, ![X52, X53, X54]:(~v1_relat_1(X53)|~v5_relat_1(X53,X52)|~v1_funct_1(X53)|(~r2_hidden(X54,k1_relat_1(X53))|k7_partfun1(X52,X53,X54)=k1_funct_1(X53,X54))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.20/0.47  cnf(c_0_66, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(k1_funct_1(esk5_0,X1),k1_relat_1(esk6_0))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_34])]), c_0_54])).
% 0.20/0.47  cnf(c_0_67, negated_conjecture, (r2_hidden(esk7_0,esk3_0)|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.47  cnf(c_0_68, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.47  cnf(c_0_69, negated_conjecture, (k1_funct_1(k8_funct_2(esk3_0,esk4_0,esk2_0,esk5_0,esk6_0),X1)=k1_funct_1(esk6_0,k1_funct_1(esk5_0,X1))|~m1_subset_1(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_33]), c_0_34]), c_0_32]), c_0_41])]), c_0_59])).
% 0.20/0.47  fof(c_0_70, plain, ![X30]:(v1_xboole_0(X30)|~v1_relat_1(X30)|~v1_xboole_0(k2_relat_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).
% 0.20/0.47  cnf(c_0_71, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.47  cnf(c_0_72, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.20/0.47  cnf(c_0_73, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  fof(c_0_74, plain, ![X7]:(~v1_xboole_0(X7)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.47  fof(c_0_75, plain, ![X11, X12]:(~v1_xboole_0(X11)|v1_xboole_0(k2_zfmisc_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).
% 0.20/0.47  fof(c_0_76, plain, ![X49, X50, X51]:(((v1_funct_1(X51)|(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|(v1_xboole_0(X49)|v1_xboole_0(X50)))&(~v1_xboole_0(X51)|(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|(v1_xboole_0(X49)|v1_xboole_0(X50))))&(v1_funct_2(X51,X49,X50)|(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X50))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|(v1_xboole_0(X49)|v1_xboole_0(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.20/0.47  fof(c_0_77, plain, ![X34]:(~v1_xboole_0(X34)|v1_funct_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.20/0.47  cnf(c_0_78, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.47  cnf(c_0_79, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|esk4_0=k1_xboole_0|r2_hidden(k1_funct_1(esk5_0,esk7_0),k1_relat_1(esk6_0))|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.47  cnf(c_0_80, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_25])).
% 0.20/0.47  cnf(c_0_81, negated_conjecture, (k1_funct_1(k8_funct_2(esk3_0,esk4_0,esk2_0,esk5_0,esk6_0),esk7_0)!=k7_partfun1(esk2_0,esk6_0,k1_funct_1(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_82, negated_conjecture, (k1_funct_1(k8_funct_2(esk3_0,esk4_0,esk2_0,esk5_0,esk6_0),esk7_0)=k1_funct_1(esk6_0,k1_funct_1(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_69, c_0_56])).
% 0.20/0.47  cnf(c_0_83, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.47  cnf(c_0_84, plain, (k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.47  cnf(c_0_85, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.47  cnf(c_0_86, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,k1_relat_1(esk6_0)))), inference(spm,[status(thm)],[c_0_73, c_0_53])).
% 0.20/0.47  cnf(c_0_87, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.47  cnf(c_0_88, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.47  cnf(c_0_89, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.47  cnf(c_0_90, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.47  cnf(c_0_91, negated_conjecture, (k7_partfun1(X1,esk6_0,k1_funct_1(esk5_0,esk7_0))=k1_funct_1(esk6_0,k1_funct_1(esk5_0,esk7_0))|k1_relat_1(esk6_0)=k1_xboole_0|esk4_0=k1_xboole_0|v1_xboole_0(esk3_0)|~v5_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_45]), c_0_80])])).
% 0.20/0.47  cnf(c_0_92, negated_conjecture, (v5_relat_1(esk6_0,esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_25])).
% 0.20/0.47  cnf(c_0_93, negated_conjecture, (k7_partfun1(esk2_0,esk6_0,k1_funct_1(esk5_0,esk7_0))!=k1_funct_1(esk6_0,k1_funct_1(esk5_0,esk7_0))), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.47  cnf(c_0_94, plain, (v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_64]), c_0_85])])).
% 0.20/0.47  cnf(c_0_95, negated_conjecture, (k2_zfmisc_1(esk3_0,k1_relat_1(esk6_0))=esk5_0|esk4_0=k1_xboole_0|~r1_tarski(k2_zfmisc_1(esk3_0,k1_relat_1(esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_86])).
% 0.20/0.47  cnf(c_0_96, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.20/0.47  cnf(c_0_97, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.47  cnf(c_0_98, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|esk4_0=k1_xboole_0|v1_xboole_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 0.20/0.47  cnf(c_0_99, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_94])).
% 0.20/0.47  cnf(c_0_100, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|~v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_61])])).
% 0.20/0.47  cnf(c_0_101, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_32]), c_0_33])]), c_0_46])).
% 0.20/0.47  cnf(c_0_102, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_98]), c_0_99]), c_0_99]), c_0_61])]), c_0_100])).
% 0.20/0.47  cnf(c_0_103, negated_conjecture, (esk4_0=k1_xboole_0|v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_85])])).
% 0.20/0.47  cnf(c_0_104, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_103]), c_0_59])).
% 0.20/0.47  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_104]), c_0_85])]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 106
% 0.20/0.47  # Proof object clause steps            : 66
% 0.20/0.47  # Proof object formula steps           : 40
% 0.20/0.47  # Proof object conjectures             : 37
% 0.20/0.47  # Proof object clause conjectures      : 34
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 32
% 0.20/0.47  # Proof object initial formulas used   : 20
% 0.20/0.47  # Proof object generating inferences   : 29
% 0.20/0.47  # Proof object simplifying inferences  : 48
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 27
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 49
% 0.20/0.47  # Removed in clause preprocessing      : 4
% 0.20/0.47  # Initial clauses in saturation        : 45
% 0.20/0.47  # Processed clauses                    : 1016
% 0.20/0.47  # ...of these trivial                  : 22
% 0.20/0.47  # ...subsumed                          : 390
% 0.20/0.47  # ...remaining for further processing  : 604
% 0.20/0.47  # Other redundant clauses eliminated   : 2
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 41
% 0.20/0.47  # Backward-rewritten                   : 339
% 0.20/0.47  # Generated clauses                    : 2260
% 0.20/0.47  # ...of the previous two non-trivial   : 1646
% 0.20/0.47  # Contextual simplify-reflections      : 19
% 0.20/0.47  # Paramodulations                      : 2256
% 0.20/0.47  # Factorizations                       : 0
% 0.20/0.47  # Equation resolutions                 : 4
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 178
% 0.20/0.47  #    Positive orientable unit clauses  : 59
% 0.20/0.47  #    Positive unorientable unit clauses: 2
% 0.20/0.47  #    Negative unit clauses             : 2
% 0.20/0.47  #    Non-unit-clauses                  : 115
% 0.20/0.47  # Current number of unprocessed clauses: 507
% 0.20/0.47  # ...number of literals in the above   : 1796
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 424
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 19150
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 7059
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 398
% 0.20/0.47  # Unit Clause-clause subsumption calls : 1668
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 100
% 0.20/0.47  # BW rewrite match successes           : 17
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 42106
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.119 s
% 0.20/0.47  # System time              : 0.005 s
% 0.20/0.47  # Total time               : 0.124 s
% 0.20/0.47  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
