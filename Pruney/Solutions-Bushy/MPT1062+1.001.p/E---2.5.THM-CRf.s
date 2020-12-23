%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1062+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:40 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 144 expanded)
%              Number of clauses        :   31 (  50 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  272 (1165 expanded)
%              Number of equality atoms :   22 (  52 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   97 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t179_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))
                     => ( r1_tarski(X4,X5)
                       => r1_tarski(k6_funct_2(X1,X2,X3,X4),k6_funct_2(X1,X2,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_funct_2)).

fof(d10_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))
                     => ( X5 = k6_funct_2(X1,X2,X3,X4)
                      <=> ! [X6] :
                            ( m1_subset_1(X6,k1_zfmisc_1(X1))
                           => ( r2_hidden(X6,X5)
                            <=> ? [X7] :
                                  ( m1_subset_1(X7,k1_zfmisc_1(X2))
                                  & r2_hidden(X7,X4)
                                  & X6 = k8_relset_1(X1,X2,X3,X7) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_funct_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(dt_k6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) )
     => m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))
                       => ( r1_tarski(X4,X5)
                         => r1_tarski(k6_funct_2(X1,X2,X3,X4),k6_funct_2(X1,X2,X3,X5)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t179_funct_2])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11,X12,X13,X15,X17] :
      ( ( m1_subset_1(esk1_6(X8,X9,X10,X11,X12,X13),k1_zfmisc_1(X9))
        | ~ r2_hidden(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X8))
        | X12 != k6_funct_2(X8,X9,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X8)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8) )
      & ( r2_hidden(esk1_6(X8,X9,X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X8))
        | X12 != k6_funct_2(X8,X9,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X8)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8) )
      & ( X13 = k8_relset_1(X8,X9,X10,esk1_6(X8,X9,X10,X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X8))
        | X12 != k6_funct_2(X8,X9,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X8)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8) )
      & ( ~ m1_subset_1(X15,k1_zfmisc_1(X9))
        | ~ r2_hidden(X15,X11)
        | X13 != k8_relset_1(X8,X9,X10,X15)
        | r2_hidden(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X8))
        | X12 != k6_funct_2(X8,X9,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X8)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8) )
      & ( m1_subset_1(esk2_5(X8,X9,X10,X11,X12),k1_zfmisc_1(X8))
        | X12 = k6_funct_2(X8,X9,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X8)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8) )
      & ( ~ r2_hidden(esk2_5(X8,X9,X10,X11,X12),X12)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X9))
        | ~ r2_hidden(X17,X11)
        | esk2_5(X8,X9,X10,X11,X12) != k8_relset_1(X8,X9,X10,X17)
        | X12 = k6_funct_2(X8,X9,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X8)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8) )
      & ( m1_subset_1(esk3_5(X8,X9,X10,X11,X12),k1_zfmisc_1(X9))
        | r2_hidden(esk2_5(X8,X9,X10,X11,X12),X12)
        | X12 = k6_funct_2(X8,X9,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X8)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8) )
      & ( r2_hidden(esk3_5(X8,X9,X10,X11,X12),X11)
        | r2_hidden(esk2_5(X8,X9,X10,X11,X12),X12)
        | X12 = k6_funct_2(X8,X9,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X8)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8) )
      & ( esk2_5(X8,X9,X10,X11,X12) = k8_relset_1(X8,X9,X10,esk3_5(X8,X9,X10,X11,X12))
        | r2_hidden(esk2_5(X8,X9,X10,X11,X12),X12)
        | X12 = k6_funct_2(X8,X9,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X8)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_funct_2])])])])])])).

fof(c_0_8,plain,(
    ! [X33,X34,X35] :
      ( ~ r2_hidden(X33,X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | m1_subset_1(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_9,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | m1_subset_1(k8_relset_1(X29,X30,X31,X32),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_10,plain,(
    ! [X25,X26,X27,X28] :
      ( v1_xboole_0(X25)
      | v1_xboole_0(X26)
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,X25,X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X26)))
      | m1_subset_1(k6_funct_2(X25,X26,X27,X28),k1_zfmisc_1(k1_zfmisc_1(X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    & ~ v1_xboole_0(esk6_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))
    & r1_tarski(esk8_0,esk9_0)
    & ~ r1_tarski(k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_12,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r1_tarski(X19,X20)
        | ~ r2_hidden(X21,X19)
        | r2_hidden(X21,X20) )
      & ( r2_hidden(esk4_2(X22,X23),X22)
        | r1_tarski(X22,X23) )
      & ( ~ r2_hidden(esk4_2(X22,X23),X23)
        | r1_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X4,X7)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k8_relset_1(X5,X2,X6,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | X7 != k6_funct_2(X5,X2,X6,X3)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X5,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X6,X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
    | X5 != k6_funct_2(X1,X2,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(k8_relset_1(X1,X2,X3,X4),k6_funct_2(X1,X2,X3,X5))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_13,c_0_14])])]),c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_6(X1,X2,X3,X4,k6_funct_2(X1,X2,X3,X4),X5),X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k6_funct_2(X1,X2,X3,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_17,c_0_14])]),c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_2(k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0)),k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k8_relset_1(esk5_0,esk6_0,esk7_0,X1),k6_funct_2(esk5_0,esk6_0,esk7_0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk6_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),esk4_2(k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0))),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_21]),c_0_30]),c_0_22]),c_0_23])]),c_0_25]),c_0_24])).

cnf(c_0_35,plain,
    ( X1 = k8_relset_1(X2,X3,X4,esk1_6(X2,X3,X4,X5,X6,X1))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | X6 != k6_funct_2(X2,X3,X4,X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k8_relset_1(esk5_0,esk6_0,esk7_0,X1),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),esk4_2(k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k8_relset_1(X1,X2,X3,esk1_6(X1,X2,X3,X4,k6_funct_2(X1,X2,X3,X4),X5)) = X5
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k6_funct_2(X1,X2,X3,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_35,c_0_14])]),c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k8_relset_1(esk5_0,esk6_0,esk7_0,esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),esk4_2(k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0)))),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( k8_relset_1(esk5_0,esk6_0,esk7_0,esk1_6(esk5_0,esk6_0,esk7_0,esk8_0,k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),esk4_2(k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0)))) = esk4_2(k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_21]),c_0_30]),c_0_22]),c_0_23])]),c_0_25]),c_0_24])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_2(k6_funct_2(esk5_0,esk6_0,esk7_0,esk8_0),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0)),k6_funct_2(esk5_0,esk6_0,esk7_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_18]),
    [proof]).

%------------------------------------------------------------------------------
