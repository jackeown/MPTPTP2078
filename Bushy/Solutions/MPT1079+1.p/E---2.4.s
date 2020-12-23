%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t196_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:40 EDT 2019

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 138 expanded)
%              Number of clauses        :   32 (  46 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  331 ( 969 expanded)
%              Number of equality atoms :   31 (  94 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   34 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t196_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5) = k4_tarski(k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5),k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t196_funct_2.p',t196_funct_2)).

fof(dt_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t196_funct_2.p',dt_k3_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t196_funct_2.p',t2_subset)).

fof(d7_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X1,X3)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) )
                     => ( X5 = k5_funct_2(X1,X2,X3,X4)
                      <=> ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => k3_funct_2(X1,X3,X5,X6) = k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t196_funct_2.p',d7_funct_2)).

fof(dt_k5_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X3)
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
     => ( v1_funct_1(k5_funct_2(X1,X2,X3,X4))
        & v1_funct_2(k5_funct_2(X1,X2,X3,X4),X1,X3)
        & m1_subset_1(k5_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t196_funct_2.p',dt_k5_funct_2)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t196_funct_2.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t196_funct_2.p',fc6_relat_1)).

fof(d6_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X1,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                     => ( X5 = k4_funct_2(X1,X2,X3,X4)
                      <=> ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => k3_funct_2(X1,X2,X5,X6) = k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t196_funct_2.p',d6_funct_2)).

fof(dt_k4_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X3)
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
     => ( v1_funct_1(k4_funct_2(X1,X2,X3,X4))
        & v1_funct_2(k4_funct_2(X1,X2,X3,X4),X1,X2)
        & m1_subset_1(k4_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t196_funct_2.p',dt_k4_funct_2)).

fof(fc10_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t196_funct_2.p',fc10_subset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5) = k4_tarski(k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5),k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t196_funct_2])).

fof(c_0_11,plain,(
    ! [X30,X31,X32,X33] :
      ( v1_xboole_0(X30)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,X30,X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | ~ m1_subset_1(X33,X30)
      | m1_subset_1(k3_funct_2(X30,X31,X32,X33),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,k2_zfmisc_1(esk2_0,esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))))
    & m1_subset_1(esk5_0,esk1_0)
    & k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0) != k4_tarski(k3_funct_2(esk1_0,esk2_0,k4_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0),k3_funct_2(esk1_0,esk3_0,k5_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X60,X61] :
      ( ~ m1_subset_1(X60,X61)
      | v1_xboole_0(X61)
      | r2_hidden(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,X1),k2_zfmisc_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

fof(c_0_21,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( X25 != k5_funct_2(X21,X22,X23,X24)
        | ~ m1_subset_1(X26,X21)
        | k3_funct_2(X21,X23,X25,X26) = k2_mcart_1(k3_funct_2(X21,k2_zfmisc_1(X22,X23),X24,X26))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X21,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X23)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,k2_zfmisc_1(X22,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,k2_zfmisc_1(X22,X23))))
        | v1_xboole_0(X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X21) )
      & ( m1_subset_1(esk7_5(X21,X22,X23,X24,X25),X21)
        | X25 = k5_funct_2(X21,X22,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X21,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X23)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,k2_zfmisc_1(X22,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,k2_zfmisc_1(X22,X23))))
        | v1_xboole_0(X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X21) )
      & ( k3_funct_2(X21,X23,X25,esk7_5(X21,X22,X23,X24,X25)) != k2_mcart_1(k3_funct_2(X21,k2_zfmisc_1(X22,X23),X24,esk7_5(X21,X22,X23,X24,X25)))
        | X25 = k5_funct_2(X21,X22,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X21,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X23)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,k2_zfmisc_1(X22,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,k2_zfmisc_1(X22,X23))))
        | v1_xboole_0(X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_funct_2])])])])])])).

fof(c_0_22,plain,(
    ! [X38,X39,X40,X41] :
      ( ( v1_funct_1(k5_funct_2(X38,X39,X40,X41))
        | v1_xboole_0(X38)
        | v1_xboole_0(X39)
        | v1_xboole_0(X40)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,k2_zfmisc_1(X39,X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,k2_zfmisc_1(X39,X40)))) )
      & ( v1_funct_2(k5_funct_2(X38,X39,X40,X41),X38,X40)
        | v1_xboole_0(X38)
        | v1_xboole_0(X39)
        | v1_xboole_0(X40)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,k2_zfmisc_1(X39,X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,k2_zfmisc_1(X39,X40)))) )
      & ( m1_subset_1(k5_funct_2(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(X38,X40)))
        | v1_xboole_0(X38)
        | v1_xboole_0(X39)
        | v1_xboole_0(X40)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X38,k2_zfmisc_1(X39,X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,k2_zfmisc_1(X39,X40)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_funct_2])])])])).

fof(c_0_23,plain,(
    ! [X58,X59] :
      ( ~ v1_relat_1(X59)
      | ~ r2_hidden(X58,X59)
      | X58 = k4_tarski(k1_mcart_1(X58),k2_mcart_1(X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,X1),k2_zfmisc_1(esk2_0,esk3_0))
    | v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_26,plain,(
    ! [X77,X78] : v1_relat_1(k2_zfmisc_1(X77,X78)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_27,plain,
    ( k3_funct_2(X2,X4,X1,X6) = k2_mcart_1(k3_funct_2(X2,k2_zfmisc_1(X3,X4),X5,X6))
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | X1 != k5_funct_2(X2,X3,X4,X5)
    | ~ m1_subset_1(X6,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X2,k2_zfmisc_1(X3,X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v1_funct_1(k5_funct_2(X1,X2,X3,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( v1_funct_2(k5_funct_2(X1,X2,X3,X4),X1,X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(k5_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( X18 != k4_funct_2(X14,X15,X16,X17)
        | ~ m1_subset_1(X19,X14)
        | k3_funct_2(X14,X15,X18,X19) = k1_mcart_1(k3_funct_2(X14,k2_zfmisc_1(X15,X16),X17,X19))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X14,X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16))))
        | v1_xboole_0(X16)
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) )
      & ( m1_subset_1(esk6_5(X14,X15,X16,X17,X18),X14)
        | X18 = k4_funct_2(X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X14,X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16))))
        | v1_xboole_0(X16)
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) )
      & ( k3_funct_2(X14,X15,X18,esk6_5(X14,X15,X16,X17,X18)) != k1_mcart_1(k3_funct_2(X14,k2_zfmisc_1(X15,X16),X17,esk6_5(X14,X15,X16,X17,X18)))
        | X18 = k4_funct_2(X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X14,X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16))))
        | v1_xboole_0(X16)
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_funct_2])])])])])])).

fof(c_0_32,plain,(
    ! [X34,X35,X36,X37] :
      ( ( v1_funct_1(k4_funct_2(X34,X35,X36,X37))
        | v1_xboole_0(X34)
        | v1_xboole_0(X35)
        | v1_xboole_0(X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,k2_zfmisc_1(X35,X36))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,k2_zfmisc_1(X35,X36)))) )
      & ( v1_funct_2(k4_funct_2(X34,X35,X36,X37),X34,X35)
        | v1_xboole_0(X34)
        | v1_xboole_0(X35)
        | v1_xboole_0(X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,k2_zfmisc_1(X35,X36))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,k2_zfmisc_1(X35,X36)))) )
      & ( m1_subset_1(k4_funct_2(X34,X35,X36,X37),k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | v1_xboole_0(X34)
        | v1_xboole_0(X35)
        | v1_xboole_0(X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,k2_zfmisc_1(X35,X36))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,k2_zfmisc_1(X35,X36)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_funct_2])])])])).

cnf(c_0_33,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0),k2_zfmisc_1(esk2_0,esk3_0))
    | v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_funct_2(X1,X2,k5_funct_2(X1,X3,X2,X4),X5) = k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X3,X2),X4,X5))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X3,X2))))
    | ~ m1_subset_1(X5,X1)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X3,X2))
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( k3_funct_2(X2,X3,X1,X6) = k1_mcart_1(k3_funct_2(X2,k2_zfmisc_1(X3,X4),X5,X6))
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | X1 != k4_funct_2(X2,X3,X4,X5)
    | ~ m1_subset_1(X6,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X2,k2_zfmisc_1(X3,X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4)))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( v1_funct_1(k4_funct_2(X1,X2,X3,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( v1_funct_2(k4_funct_2(X1,X2,X3,X4),X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( m1_subset_1(k4_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0)),k2_mcart_1(k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0))) = k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0)
    | v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( k2_mcart_1(k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,X1)) = k3_funct_2(esk1_0,esk3_0,k5_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),c_0_37]),c_0_38])).

cnf(c_0_45,plain,
    ( k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5) = k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ m1_subset_1(X5,X1)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_40]),c_0_41]),c_0_42])).

fof(c_0_46,plain,(
    ! [X75,X76] :
      ( v1_xboole_0(X75)
      | v1_xboole_0(X76)
      | ~ v1_xboole_0(k2_zfmisc_1(X75,X76)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc10_subset_1])])])).

cnf(c_0_47,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0)),k3_funct_2(esk1_0,esk3_0,k5_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)) = k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0)
    | v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_25])])).

cnf(c_0_48,negated_conjecture,
    ( k1_mcart_1(k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,X1)) = k3_funct_2(esk1_0,esk2_0,k4_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),c_0_37]),c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k3_funct_2(esk1_0,k2_zfmisc_1(esk2_0,esk3_0),esk4_0,esk5_0) != k4_tarski(k3_funct_2(esk1_0,esk2_0,k4_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0),k3_funct_2(esk1_0,esk3_0,k5_funct_2(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_25])]),c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_38]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
