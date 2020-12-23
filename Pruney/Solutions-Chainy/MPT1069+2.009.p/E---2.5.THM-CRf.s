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
% DateTime   : Thu Dec  3 11:07:50 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 286 expanded)
%              Number of clauses        :   61 ( 111 expanded)
%              Number of leaves         :   18 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  348 (1703 expanded)
%              Number of equality atoms :   82 ( 366 expanded)
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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    ! [X59,X60,X61] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | k1_relset_1(X59,X60,X61) = k1_relat_1(X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0)
    & v1_funct_1(esk10_0)
    & v1_funct_2(esk10_0,esk8_0,esk9_0)
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))
    & v1_funct_1(esk11_0)
    & m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk7_0)))
    & m1_subset_1(esk12_0,esk8_0)
    & r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relset_1(esk9_0,esk7_0,esk11_0))
    & esk8_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0) != k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X86,X87,X88,X89] :
      ( ( v1_funct_1(X89)
        | X87 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X86,X87,X89),X88)
        | ~ v1_funct_1(X89)
        | ~ v1_funct_2(X89,X86,X87)
        | ~ m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) )
      & ( v1_funct_2(X89,X86,X88)
        | X87 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X86,X87,X89),X88)
        | ~ v1_funct_1(X89)
        | ~ v1_funct_2(X89,X86,X87)
        | ~ m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) )
      & ( m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X88)))
        | X87 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X86,X87,X89),X88)
        | ~ v1_funct_1(X89)
        | ~ v1_funct_2(X89,X86,X87)
        | ~ m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) )
      & ( v1_funct_1(X89)
        | X86 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X86,X87,X89),X88)
        | ~ v1_funct_1(X89)
        | ~ v1_funct_2(X89,X86,X87)
        | ~ m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) )
      & ( v1_funct_2(X89,X86,X88)
        | X86 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X86,X87,X89),X88)
        | ~ v1_funct_1(X89)
        | ~ v1_funct_2(X89,X86,X87)
        | ~ m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) )
      & ( m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X88)))
        | X86 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X86,X87,X89),X88)
        | ~ v1_funct_1(X89)
        | ~ v1_funct_2(X89,X86,X87)
        | ~ m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relset_1(esk9_0,esk7_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k1_relset_1(esk9_0,esk7_0,esk11_0) = k1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk10_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X20,X21)
      | v1_xboole_0(X21)
      | r2_hidden(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_31,plain,(
    ! [X82,X83,X84,X85] :
      ( ~ v1_funct_1(X85)
      | ~ v1_funct_2(X85,X82,X83)
      | ~ m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))
      | ~ r2_hidden(X84,X82)
      | X83 = k1_xboole_0
      | r2_hidden(k1_funct_1(X85,X84),X83) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relat_1(esk11_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | v1_funct_2(esk10_0,esk8_0,X1)
    | ~ r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

fof(c_0_35,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk12_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_38,plain,(
    ! [X72,X73,X74,X75,X76,X77] :
      ( v1_xboole_0(X74)
      | ~ v1_funct_1(X75)
      | ~ v1_funct_2(X75,X73,X74)
      | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))
      | ~ v1_funct_1(X76)
      | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X72)))
      | ~ m1_subset_1(X77,X73)
      | ~ r1_tarski(k2_relset_1(X73,X74,X75),k1_relset_1(X74,X72,X76))
      | X73 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X73,X74,X72,X75,X76),X77) = k1_funct_1(X76,k1_funct_1(X75,X77)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

fof(c_0_39,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_28]),c_0_29]),c_0_27])])).

cnf(c_0_42,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | v1_funct_2(esk10_0,esk8_0,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk12_0,esk8_0)
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_46,plain,(
    ! [X50,X51,X52] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | v1_relat_1(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_47,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_50,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_52,plain,(
    ! [X69,X70,X71] :
      ( ~ v1_relat_1(X70)
      | ~ v5_relat_1(X70,X69)
      | ~ v1_funct_1(X70)
      | ~ r2_hidden(X71,k1_relat_1(X70))
      | k7_partfun1(X69,X70,X71) = k1_funct_1(X70,X71) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk11_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk10_0,X1),k1_relat_1(esk11_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_29])]),c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk12_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_55,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_56,plain,(
    ! [X53,X54,X55] :
      ( ( v4_relat_1(X55,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( v5_relat_1(X55,X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk9_0,esk7_0,X2,esk11_0),X3) = k1_funct_1(esk11_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk9_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk9_0)))
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(k2_relset_1(X1,esk9_0,X2),k1_relat_1(esk11_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_22]),c_0_48]),c_0_25])]),c_0_49])).

fof(c_0_58,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | ~ v1_xboole_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( k1_relat_1(esk11_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk10_0,esk12_0),k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_22])).

cnf(c_0_64,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),X1) = k1_funct_1(esk11_0,k1_funct_1(esk10_0,X1))
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_29]),c_0_27]),c_0_33])]),c_0_45])).

fof(c_0_66,plain,(
    ! [X66,X67,X68] :
      ( ( v1_funct_1(X68)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | v1_xboole_0(X66)
        | v1_xboole_0(X67) )
      & ( ~ v1_xboole_0(X68)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | v1_xboole_0(X66)
        | v1_xboole_0(X67) )
      & ( v1_funct_2(X68,X66,X67)
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | v1_xboole_0(X66)
        | v1_xboole_0(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

fof(c_0_67,plain,(
    ! [X37] :
      ( ~ v1_xboole_0(X37)
      | v1_funct_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_71,negated_conjecture,
    ( k7_partfun1(X1,esk11_0,k1_funct_1(esk10_0,esk12_0)) = k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))
    | k1_relat_1(esk11_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | ~ v5_relat_1(esk11_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_48]),c_0_63])])).

cnf(c_0_72,negated_conjecture,
    ( v5_relat_1(esk11_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_22])).

cnf(c_0_73,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0) != k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0) = k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_37])).

fof(c_0_75,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_76,plain,(
    ! [X17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_80,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_81,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_41])).

cnf(c_0_82,negated_conjecture,
    ( k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0)) = k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))
    | k1_relat_1(esk11_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0)) != k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_54])).

cnf(c_0_88,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0)) = esk10_0
    | esk9_0 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0)),esk10_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( k1_relat_1(esk11_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_91,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( ~ v1_xboole_0(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_27]),c_0_28])]),c_0_49]),c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_90]),c_0_91])])).

cnf(c_0_94,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_95,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_95]),c_0_94])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.57  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.20/0.57  # and selection function SelectNewComplexAHP.
% 0.20/0.57  #
% 0.20/0.57  # Preprocessing time       : 0.030 s
% 0.20/0.57  # Presaturation interreduction done
% 0.20/0.57  
% 0.20/0.57  # Proof found!
% 0.20/0.57  # SZS status Theorem
% 0.20/0.57  # SZS output start CNFRefutation
% 0.20/0.57  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 0.20/0.57  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.57  fof(t8_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 0.20/0.57  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.57  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 0.20/0.57  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.57  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 0.20/0.57  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.57  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.57  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.57  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 0.20/0.57  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.57  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.57  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.20/0.57  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.20/0.57  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.57  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.57  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.57  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.20/0.57  fof(c_0_19, plain, ![X59, X60, X61]:(~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|k1_relset_1(X59,X60,X61)=k1_relat_1(X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.57  fof(c_0_20, negated_conjecture, (~v1_xboole_0(esk9_0)&(((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk8_0,esk9_0))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))))&((v1_funct_1(esk11_0)&m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk7_0))))&(m1_subset_1(esk12_0,esk8_0)&(r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relset_1(esk9_0,esk7_0,esk11_0))&(esk8_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0)!=k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.20/0.57  cnf(c_0_21, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.57  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  fof(c_0_23, plain, ![X86, X87, X88, X89]:((((v1_funct_1(X89)|X87=k1_xboole_0|~r1_tarski(k2_relset_1(X86,X87,X89),X88)|(~v1_funct_1(X89)|~v1_funct_2(X89,X86,X87)|~m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87)))))&(v1_funct_2(X89,X86,X88)|X87=k1_xboole_0|~r1_tarski(k2_relset_1(X86,X87,X89),X88)|(~v1_funct_1(X89)|~v1_funct_2(X89,X86,X87)|~m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87))))))&(m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X88)))|X87=k1_xboole_0|~r1_tarski(k2_relset_1(X86,X87,X89),X88)|(~v1_funct_1(X89)|~v1_funct_2(X89,X86,X87)|~m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87))))))&(((v1_funct_1(X89)|X86!=k1_xboole_0|~r1_tarski(k2_relset_1(X86,X87,X89),X88)|(~v1_funct_1(X89)|~v1_funct_2(X89,X86,X87)|~m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87)))))&(v1_funct_2(X89,X86,X88)|X86!=k1_xboole_0|~r1_tarski(k2_relset_1(X86,X87,X89),X88)|(~v1_funct_1(X89)|~v1_funct_2(X89,X86,X87)|~m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87))))))&(m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X88)))|X86!=k1_xboole_0|~r1_tarski(k2_relset_1(X86,X87,X89),X88)|(~v1_funct_1(X89)|~v1_funct_2(X89,X86,X87)|~m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(X86,X87))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).
% 0.20/0.57  cnf(c_0_24, negated_conjecture, (r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relset_1(esk9_0,esk7_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  cnf(c_0_25, negated_conjecture, (k1_relset_1(esk9_0,esk7_0,esk11_0)=k1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.57  cnf(c_0_26, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.57  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk10_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  fof(c_0_30, plain, ![X20, X21]:(~m1_subset_1(X20,X21)|(v1_xboole_0(X21)|r2_hidden(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.57  fof(c_0_31, plain, ![X82, X83, X84, X85]:(~v1_funct_1(X85)|~v1_funct_2(X85,X82,X83)|~m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))|(~r2_hidden(X84,X82)|(X83=k1_xboole_0|r2_hidden(k1_funct_1(X85,X84),X83)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.20/0.57  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.57  cnf(c_0_33, negated_conjecture, (r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),k1_relat_1(esk11_0))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.57  cnf(c_0_34, negated_conjecture, (esk9_0=k1_xboole_0|v1_funct_2(esk10_0,esk8_0,X1)|~r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.20/0.57  fof(c_0_35, plain, ![X7]:(~v1_xboole_0(X7)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.57  cnf(c_0_36, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.57  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk12_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  fof(c_0_38, plain, ![X72, X73, X74, X75, X76, X77]:(v1_xboole_0(X74)|(~v1_funct_1(X75)|~v1_funct_2(X75,X73,X74)|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))|(~v1_funct_1(X76)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X72)))|(~m1_subset_1(X77,X73)|(~r1_tarski(k2_relset_1(X73,X74,X75),k1_relset_1(X74,X72,X76))|(X73=k1_xboole_0|k1_funct_1(k8_funct_2(X73,X74,X72,X75,X76),X77)=k1_funct_1(X76,k1_funct_1(X75,X77)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.20/0.57  fof(c_0_39, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.57  cnf(c_0_40, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.57  cnf(c_0_41, negated_conjecture, (esk9_0=k1_xboole_0|m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_28]), c_0_29]), c_0_27])])).
% 0.20/0.57  cnf(c_0_42, negated_conjecture, (esk9_0=k1_xboole_0|v1_funct_2(esk10_0,esk8_0,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 0.20/0.57  cnf(c_0_43, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.57  cnf(c_0_44, negated_conjecture, (r2_hidden(esk12_0,esk8_0)|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.57  cnf(c_0_45, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  fof(c_0_46, plain, ![X50, X51, X52]:(~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|v1_relat_1(X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.57  cnf(c_0_47, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.57  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  fof(c_0_50, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.57  cnf(c_0_51, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.57  fof(c_0_52, plain, ![X69, X70, X71]:(~v1_relat_1(X70)|~v5_relat_1(X70,X69)|~v1_funct_1(X70)|(~r2_hidden(X71,k1_relat_1(X70))|k7_partfun1(X69,X70,X71)=k1_funct_1(X70,X71))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.20/0.57  cnf(c_0_53, negated_conjecture, (k1_relat_1(esk11_0)=k1_xboole_0|esk9_0=k1_xboole_0|r2_hidden(k1_funct_1(esk10_0,X1),k1_relat_1(esk11_0))|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_29])]), c_0_42])).
% 0.20/0.57  cnf(c_0_54, negated_conjecture, (r2_hidden(esk12_0,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.20/0.57  cnf(c_0_55, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.57  fof(c_0_56, plain, ![X53, X54, X55]:((v4_relat_1(X55,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))&(v5_relat_1(X55,X54)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.57  cnf(c_0_57, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk9_0,esk7_0,X2,esk11_0),X3)=k1_funct_1(esk11_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~v1_funct_2(X2,X1,esk9_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk9_0)))|~m1_subset_1(X3,X1)|~r1_tarski(k2_relset_1(X1,esk9_0,X2),k1_relat_1(esk11_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_22]), c_0_48]), c_0_25])]), c_0_49])).
% 0.20/0.57  fof(c_0_58, plain, ![X27, X28, X29]:(~r2_hidden(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(X29))|~v1_xboole_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.57  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.57  cnf(c_0_60, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_51])).
% 0.20/0.57  cnf(c_0_61, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.57  cnf(c_0_62, negated_conjecture, (k1_relat_1(esk11_0)=k1_xboole_0|esk9_0=k1_xboole_0|r2_hidden(k1_funct_1(esk10_0,esk12_0),k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.57  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_55, c_0_22])).
% 0.20/0.57  cnf(c_0_64, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.57  cnf(c_0_65, negated_conjecture, (k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),X1)=k1_funct_1(esk11_0,k1_funct_1(esk10_0,X1))|~m1_subset_1(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_28]), c_0_29]), c_0_27]), c_0_33])]), c_0_45])).
% 0.20/0.57  fof(c_0_66, plain, ![X66, X67, X68]:(((v1_funct_1(X68)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67))|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))|(v1_xboole_0(X66)|v1_xboole_0(X67)))&(~v1_xboole_0(X68)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67))|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))|(v1_xboole_0(X66)|v1_xboole_0(X67))))&(v1_funct_2(X68,X66,X67)|(~v1_funct_1(X68)|~v1_funct_2(X68,X66,X67))|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))|(v1_xboole_0(X66)|v1_xboole_0(X67)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.20/0.57  fof(c_0_67, plain, ![X37]:(~v1_xboole_0(X37)|v1_funct_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.20/0.57  cnf(c_0_68, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.57  cnf(c_0_69, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.57  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.57  cnf(c_0_71, negated_conjecture, (k7_partfun1(X1,esk11_0,k1_funct_1(esk10_0,esk12_0))=k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))|k1_relat_1(esk11_0)=k1_xboole_0|esk9_0=k1_xboole_0|~v5_relat_1(esk11_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_48]), c_0_63])])).
% 0.20/0.57  cnf(c_0_72, negated_conjecture, (v5_relat_1(esk11_0,esk7_0)), inference(spm,[status(thm)],[c_0_64, c_0_22])).
% 0.20/0.57  cnf(c_0_73, negated_conjecture, (k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0)!=k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  cnf(c_0_74, negated_conjecture, (k1_funct_1(k8_funct_2(esk8_0,esk9_0,esk7_0,esk10_0,esk11_0),esk12_0)=k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))), inference(spm,[status(thm)],[c_0_65, c_0_37])).
% 0.20/0.57  fof(c_0_75, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.57  fof(c_0_76, plain, ![X17]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.57  cnf(c_0_77, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.57  cnf(c_0_78, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.57  cnf(c_0_79, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.57  cnf(c_0_80, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.57  cnf(c_0_81, negated_conjecture, (esk9_0=k1_xboole_0|r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0)))), inference(spm,[status(thm)],[c_0_70, c_0_41])).
% 0.20/0.57  cnf(c_0_82, negated_conjecture, (k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0))=k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))|k1_relat_1(esk11_0)=k1_xboole_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.57  cnf(c_0_83, negated_conjecture, (k7_partfun1(esk7_0,esk11_0,k1_funct_1(esk10_0,esk12_0))!=k1_funct_1(esk11_0,k1_funct_1(esk10_0,esk12_0))), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.57  cnf(c_0_84, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.57  cnf(c_0_85, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.57  cnf(c_0_86, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.57  cnf(c_0_87, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_79, c_0_54])).
% 0.20/0.57  cnf(c_0_88, negated_conjecture, (k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0))=esk10_0|esk9_0=k1_xboole_0|~r1_tarski(k2_zfmisc_1(esk8_0,k1_relat_1(esk11_0)),esk10_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.57  cnf(c_0_89, negated_conjecture, (k1_relat_1(esk11_0)=k1_xboole_0|esk9_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.57  cnf(c_0_90, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_84])).
% 0.20/0.57  cnf(c_0_91, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_70, c_0_85])).
% 0.20/0.57  cnf(c_0_92, negated_conjecture, (~v1_xboole_0(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_27]), c_0_28])]), c_0_49]), c_0_87])).
% 0.20/0.57  cnf(c_0_93, negated_conjecture, (esk9_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90]), c_0_90]), c_0_91])])).
% 0.20/0.57  cnf(c_0_94, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.57  cnf(c_0_95, negated_conjecture, (esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])])).
% 0.20/0.57  cnf(c_0_96, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_95]), c_0_94])]), ['proof']).
% 0.20/0.57  # SZS output end CNFRefutation
% 0.20/0.57  # Proof object total steps             : 97
% 0.20/0.57  # Proof object clause steps            : 61
% 0.20/0.57  # Proof object formula steps           : 36
% 0.20/0.57  # Proof object conjectures             : 38
% 0.20/0.57  # Proof object clause conjectures      : 35
% 0.20/0.57  # Proof object formula conjectures     : 3
% 0.20/0.57  # Proof object initial clauses used    : 30
% 0.20/0.57  # Proof object initial formulas used   : 18
% 0.20/0.57  # Proof object generating inferences   : 25
% 0.20/0.57  # Proof object simplifying inferences  : 41
% 0.20/0.57  # Training examples: 0 positive, 0 negative
% 0.20/0.57  # Parsed axioms                        : 32
% 0.20/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.57  # Initial clauses                      : 67
% 0.20/0.57  # Removed in clause preprocessing      : 6
% 0.20/0.57  # Initial clauses in saturation        : 61
% 0.20/0.57  # Processed clauses                    : 1997
% 0.20/0.57  # ...of these trivial                  : 5
% 0.20/0.57  # ...subsumed                          : 964
% 0.20/0.57  # ...remaining for further processing  : 1028
% 0.20/0.57  # Other redundant clauses eliminated   : 2
% 0.20/0.57  # Clauses deleted for lack of memory   : 0
% 0.20/0.57  # Backward-subsumed                    : 95
% 0.20/0.57  # Backward-rewritten                   : 494
% 0.20/0.57  # Generated clauses                    : 6462
% 0.20/0.57  # ...of the previous two non-trivial   : 3915
% 0.20/0.57  # Contextual simplify-reflections      : 28
% 0.20/0.57  # Paramodulations                      : 6440
% 0.20/0.57  # Factorizations                       : 0
% 0.20/0.57  # Equation resolutions                 : 20
% 0.20/0.57  # Propositional unsat checks           : 0
% 0.20/0.57  #    Propositional check models        : 0
% 0.20/0.57  #    Propositional check unsatisfiable : 0
% 0.20/0.57  #    Propositional clauses             : 0
% 0.20/0.57  #    Propositional clauses after purity: 0
% 0.20/0.57  #    Propositional unsat core size     : 0
% 0.20/0.57  #    Propositional preprocessing time  : 0.000
% 0.20/0.57  #    Propositional encoding time       : 0.000
% 0.20/0.57  #    Propositional solver time         : 0.000
% 0.20/0.57  #    Success case prop preproc time    : 0.000
% 0.20/0.57  #    Success case prop encoding time   : 0.000
% 0.20/0.57  #    Success case prop solver time     : 0.000
% 0.20/0.57  # Current number of processed clauses  : 375
% 0.20/0.57  #    Positive orientable unit clauses  : 51
% 0.20/0.57  #    Positive unorientable unit clauses: 0
% 0.20/0.57  #    Negative unit clauses             : 13
% 0.20/0.57  #    Non-unit-clauses                  : 311
% 0.20/0.57  # Current number of unprocessed clauses: 1900
% 0.20/0.57  # ...number of literals in the above   : 9849
% 0.20/0.57  # Current number of archived formulas  : 0
% 0.20/0.57  # Current number of archived clauses   : 651
% 0.20/0.57  # Clause-clause subsumption calls (NU) : 103665
% 0.20/0.57  # Rec. Clause-clause subsumption calls : 24464
% 0.20/0.57  # Non-unit clause-clause subsumptions  : 656
% 0.20/0.57  # Unit Clause-clause subsumption calls : 3253
% 0.20/0.57  # Rewrite failures with RHS unbound    : 0
% 0.20/0.57  # BW rewrite match attempts            : 69
% 0.20/0.57  # BW rewrite match successes           : 7
% 0.20/0.57  # Condensation attempts                : 0
% 0.20/0.57  # Condensation successes               : 0
% 0.20/0.57  # Termbank termtop insertions          : 128298
% 0.20/0.57  
% 0.20/0.57  # -------------------------------------------------
% 0.20/0.57  # User time                : 0.223 s
% 0.20/0.57  # System time              : 0.010 s
% 0.20/0.57  # Total time               : 0.233 s
% 0.20/0.57  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
