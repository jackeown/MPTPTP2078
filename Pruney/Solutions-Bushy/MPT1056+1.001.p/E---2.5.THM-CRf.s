%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1056+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:40 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 277 expanded)
%              Number of clauses        :   55 ( 104 expanded)
%              Number of leaves         :   14 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  362 (2272 expanded)
%              Number of equality atoms :   55 ( 324 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t173_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X4,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => ( r2_hidden(X6,X4)
                             => k3_funct_2(X1,X2,X3,X6) = k1_funct_1(X5,X6) ) )
                       => k2_partfun1(X1,X2,X3,X4) = X5 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t113_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t38_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,X4,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                       => ( ! [X6] :
                              ( m1_subset_1(X6,X1)
                             => ( r2_hidden(X6,X4)
                               => k3_funct_2(X1,X2,X3,X6) = k1_funct_1(X5,X6) ) )
                         => k2_partfun1(X1,X2,X3,X4) = X5 ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t173_funct_2])).

fof(c_0_15,negated_conjecture,(
    ! [X50] :
      ( ~ v1_xboole_0(esk2_0)
      & ~ v1_xboole_0(esk3_0)
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk2_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & ~ v1_xboole_0(esk5_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,esk5_0,esk3_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))
      & ( ~ m1_subset_1(X50,esk2_0)
        | ~ r2_hidden(X50,esk5_0)
        | k3_funct_2(esk2_0,esk3_0,esk4_0,X50) = k1_funct_1(esk6_0,X50) )
      & k2_partfun1(esk2_0,esk3_0,esk4_0,esk5_0) != esk6_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X21] :
      ( v1_xboole_0(X18)
      | ~ v1_funct_1(X20)
      | ~ v1_funct_2(X20,X18,X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | ~ m1_subset_1(X21,X18)
      | k3_funct_2(X18,X19,X20,X21) = k1_funct_1(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_17,plain,(
    ! [X39,X40,X41] :
      ( ~ r2_hidden(X39,X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(X41))
      | m1_subset_1(X39,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_18,negated_conjecture,
    ( k3_funct_2(esk2_0,esk3_0,esk4_0,X1) = k1_funct_1(esk6_0,X1)
    | ~ m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X31,X32)
      | v1_xboole_0(X32)
      | r2_hidden(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X26,X27,X28,X29] :
      ( ( m1_subset_1(esk1_4(X26,X27,X28,X29),X26)
        | r2_relset_1(X26,X27,X28,X29)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X26,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( k1_funct_1(X28,esk1_4(X26,X27,X28,X29)) != k1_funct_1(X29,esk1_4(X26,X27,X28,X29))
        | r2_relset_1(X26,X27,X28,X29)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X26,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_funct_2])])])])])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_32,plain,(
    ! [X42,X43,X44] :
      ( ~ v1_relat_1(X44)
      | ~ v1_funct_1(X44)
      | ~ r2_hidden(X42,X43)
      | k1_funct_1(k7_relat_1(X44,X43),X42) = k1_funct_1(X44,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

fof(c_0_33,plain,(
    ! [X10,X11,X12,X13] :
      ( ( v1_funct_1(k2_partfun1(X10,X11,X12,X13))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( m1_subset_1(k2_partfun1(X10,X11,X12,X13),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_34,plain,(
    ! [X14,X15,X16,X17] :
      ( ~ v1_funct_1(X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k2_partfun1(X14,X15,X16,X17) = k7_relat_1(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_35,plain,
    ( r2_relset_1(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = k1_funct_1(esk4_0,X1)
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_30])).

cnf(c_0_39,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_43,negated_conjecture,
    ( r2_relset_1(X1,X2,X3,esk6_0)
    | k1_funct_1(X3,esk1_4(X1,X2,X3,esk6_0)) != k1_funct_1(esk4_0,esk1_4(X1,X2,X3,esk6_0))
    | ~ v1_funct_2(esk6_0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(esk1_4(X1,X2,X3,esk6_0),esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_44,plain,
    ( k1_funct_1(k7_relat_1(X1,X2),X3) = k1_funct_1(X1,X3)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X3,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_29])).

cnf(c_0_45,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_47,plain,(
    ! [X33,X34,X35,X36] :
      ( ( v1_funct_1(k2_partfun1(X33,X34,X36,X35))
        | X34 = k1_xboole_0
        | ~ r1_tarski(X35,X33)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X33,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v1_funct_2(k2_partfun1(X33,X34,X36,X35),X35,X34)
        | X34 = k1_xboole_0
        | ~ r1_tarski(X35,X33)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X33,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( m1_subset_1(k2_partfun1(X33,X34,X36,X35),k1_zfmisc_1(k2_zfmisc_1(X35,X34)))
        | X34 = k1_xboole_0
        | ~ r1_tarski(X35,X33)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X33,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v1_funct_1(k2_partfun1(X33,X34,X36,X35))
        | X33 != k1_xboole_0
        | ~ r1_tarski(X35,X33)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X33,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v1_funct_2(k2_partfun1(X33,X34,X36,X35),X35,X34)
        | X33 != k1_xboole_0
        | ~ r1_tarski(X35,X33)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X33,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( m1_subset_1(k2_partfun1(X33,X34,X36,X35),k1_zfmisc_1(k2_zfmisc_1(X35,X34)))
        | X33 != k1_xboole_0
        | ~ r1_tarski(X35,X33)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X33,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_2])])])).

cnf(c_0_48,negated_conjecture,
    ( r2_relset_1(X1,X2,k7_relat_1(X3,X4),esk6_0)
    | v1_xboole_0(X4)
    | k1_funct_1(X3,esk1_4(X1,X2,k7_relat_1(X3,X4),esk6_0)) != k1_funct_1(esk4_0,esk1_4(X1,X2,k7_relat_1(X3,X4),esk6_0))
    | ~ v1_funct_2(k7_relat_1(X3,X4),X1,X2)
    | ~ v1_funct_2(esk6_0,X1,X2)
    | ~ v1_funct_1(k7_relat_1(X3,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ m1_subset_1(esk1_4(X1,X2,k7_relat_1(X3,X4),esk6_0),esk5_0)
    | ~ m1_subset_1(esk1_4(X1,X2,k7_relat_1(X3,X4),esk6_0),X4)
    | ~ m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_22]),c_0_21])])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

fof(c_0_51,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r2_relset_1(X22,X23,X24,X25)
        | X24 = X25
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X24 != X25
        | r2_relset_1(X22,X23,X24,X25)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | X2 = k1_xboole_0
    | ~ r1_tarski(X4,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_53,plain,(
    ! [X37,X38] :
      ( ( ~ m1_subset_1(X37,k1_zfmisc_1(X38))
        | r1_tarski(X37,X38) )
      & ( ~ r1_tarski(X37,X38)
        | m1_subset_1(X37,k1_zfmisc_1(X38)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_54,negated_conjecture,
    ( r2_relset_1(X1,X2,k7_relat_1(esk4_0,X3),esk6_0)
    | v1_xboole_0(X3)
    | ~ v1_funct_2(k7_relat_1(esk4_0,X3),X1,X2)
    | ~ v1_funct_2(esk6_0,X1,X2)
    | ~ m1_subset_1(esk1_4(X1,X2,k7_relat_1(esk4_0,X3),esk6_0),esk5_0)
    | ~ m1_subset_1(esk1_4(X1,X2,k7_relat_1(esk4_0,X3),esk6_0),X3)
    | ~ m1_subset_1(k7_relat_1(esk4_0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_49]),c_0_21]),c_0_50])])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | r2_relset_1(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_56,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(X3,X4)
    | ~ v1_funct_2(X2,X4,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_41])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r2_relset_1(esk5_0,X1,k7_relat_1(esk4_0,X2),esk6_0)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(k7_relat_1(esk4_0,X2),esk5_0,X1)
    | ~ v1_funct_2(esk6_0,esk5_0,X1)
    | ~ m1_subset_1(esk1_4(esk5_0,X1,k7_relat_1(esk4_0,X2),esk6_0),X2)
    | ~ m1_subset_1(k7_relat_1(esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_37]),c_0_49])])).

cnf(c_0_61,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_relset_1(esk5_0,esk3_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( r2_relset_1(esk5_0,X1,k7_relat_1(esk4_0,esk5_0),esk6_0)
    | ~ v1_funct_2(k7_relat_1(esk4_0,esk5_0),esk5_0,X1)
    | ~ v1_funct_2(esk6_0,esk5_0,X1)
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_55]),c_0_37]),c_0_49])]),c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(esk6_0,esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = k7_relat_1(esk4_0,esk5_0)
    | esk3_0 = k1_xboole_0
    | ~ r2_relset_1(esk5_0,esk3_0,k7_relat_1(esk4_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_67,negated_conjecture,
    ( r2_relset_1(esk5_0,esk3_0,k7_relat_1(esk4_0,esk5_0),esk6_0)
    | ~ v1_funct_2(k7_relat_1(esk4_0,esk5_0),esk5_0,esk3_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_57])])).

cnf(c_0_68,negated_conjecture,
    ( k2_partfun1(esk2_0,esk3_0,esk4_0,esk5_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 = k7_relat_1(esk4_0,esk5_0)
    | esk3_0 = k1_xboole_0
    | ~ v1_funct_2(k7_relat_1(esk4_0,esk5_0),esk5_0,esk3_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,plain,
    ( v1_funct_2(k2_partfun1(X1,X2,X3,X4),X4,X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X4,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k2_partfun1(esk2_0,esk3_0,esk4_0,esk5_0) != k7_relat_1(esk4_0,esk5_0)
    | ~ v1_funct_2(k7_relat_1(esk4_0,esk5_0),esk5_0,esk3_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(X2,X3),X3,X1)
    | ~ r1_tarski(X3,X4)
    | ~ v1_funct_2(X2,X4,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_41])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_2(k7_relat_1(esk4_0,esk5_0),esk5_0,esk3_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_41]),c_0_21]),c_0_22])])).

cnf(c_0_74,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_funct_2(k7_relat_1(esk4_0,X1),X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_75,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_63])])).

cnf(c_0_76,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_77,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_79,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_62]),c_0_63])])).

cnf(c_0_80,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_80])]),
    [proof]).

%------------------------------------------------------------------------------
