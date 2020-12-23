%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relset_1__t51_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:11 EDT 2019

% Result     : Theorem 265.54s
% Output     : CNFRefutation 265.54s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 803 expanded)
%              Number of clauses        :   54 ( 345 expanded)
%              Number of leaves         :   11 ( 187 expanded)
%              Depth                    :   14
%              Number of atoms          :  260 (4419 expanded)
%              Number of equality atoms :   15 ( 157 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t7_boole)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t106_zfmisc_1)).

fof(t51_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
                     => ! [X6,X7] :
                          ( r2_hidden(k4_tarski(X6,X7),k4_relset_1(X1,X2,X2,X3,X4,X5))
                        <=> ? [X8] :
                              ( m1_subset_1(X8,X2)
                              & r2_hidden(k4_tarski(X6,X8),X4)
                              & r2_hidden(k4_tarski(X8,X7),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t51_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t4_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',existence_m1_subset_1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',redefinition_k4_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',t1_subset)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',dt_k5_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t51_relset_1.p',cc1_relset_1)).

fof(c_0_11,plain,(
    ! [X66,X67] :
      ( ~ r2_hidden(X66,X67)
      | ~ v1_xboole_0(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_12,plain,(
    ! [X49,X50,X51,X52] :
      ( ( r2_hidden(X49,X51)
        | ~ r2_hidden(k4_tarski(X49,X50),k2_zfmisc_1(X51,X52)) )
      & ( r2_hidden(X50,X52)
        | ~ r2_hidden(k4_tarski(X49,X50),k2_zfmisc_1(X51,X52)) )
      & ( ~ r2_hidden(X49,X51)
        | ~ r2_hidden(X50,X52)
        | r2_hidden(k4_tarski(X49,X50),k2_zfmisc_1(X51,X52)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
                       => ! [X6,X7] :
                            ( r2_hidden(k4_tarski(X6,X7),k4_relset_1(X1,X2,X2,X3,X4,X5))
                          <=> ? [X8] :
                                ( m1_subset_1(X8,X2)
                                & r2_hidden(k4_tarski(X6,X8),X4)
                                & r2_hidden(k4_tarski(X8,X7),X5) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_relset_1])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X55,X56] :
      ( ~ m1_subset_1(X55,X56)
      | v1_xboole_0(X56)
      | r2_hidden(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_17,plain,(
    ! [X59,X60,X61] :
      ( ~ r2_hidden(X59,X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(X61))
      | m1_subset_1(X59,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_18,negated_conjecture,(
    ! [X16] :
      ( ~ v1_xboole_0(esk1_0)
      & ~ v1_xboole_0(esk2_0)
      & ~ v1_xboole_0(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & ( ~ r2_hidden(k4_tarski(esk6_0,esk7_0),k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0))
        | ~ m1_subset_1(X16,esk2_0)
        | ~ r2_hidden(k4_tarski(esk6_0,X16),esk4_0)
        | ~ r2_hidden(k4_tarski(X16,esk7_0),esk5_0) )
      & ( m1_subset_1(esk8_0,esk2_0)
        | r2_hidden(k4_tarski(esk6_0,esk7_0),k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0)) )
      & ( r2_hidden(k4_tarski(esk6_0,esk8_0),esk4_0)
        | r2_hidden(k4_tarski(esk6_0,esk7_0),k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0)) )
      & ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0)
        | r2_hidden(k4_tarski(esk6_0,esk7_0),k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | ~ v1_xboole_0(k2_zfmisc_1(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X41] : m1_subset_1(esk13_1(X41),X41) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_25,plain,(
    ! [X43,X44,X45,X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k4_relset_1(X43,X44,X45,X46,X47,X48) = k5_relat_1(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X5,X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk13_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_31,plain,(
    ! [X53,X54] :
      ( ~ r2_hidden(X53,X54)
      | m1_subset_1(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_32,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X3,esk1_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk13_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk7_0),k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk4_0)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k4_relset_1(X1,X2,esk2_0,esk3_0,X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(X2,esk1_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk13_1(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29])).

fof(c_0_42,plain,(
    ! [X20,X21,X22,X23,X24,X26,X27,X28,X31] :
      ( ( r2_hidden(k4_tarski(X23,esk9_5(X20,X21,X22,X23,X24)),X20)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk9_5(X20,X21,X22,X23,X24),X24),X21)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X26,X28),X20)
        | ~ r2_hidden(k4_tarski(X28,X27),X21)
        | r2_hidden(k4_tarski(X26,X27),X22)
        | X22 != k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk10_3(X20,X21,X22),esk11_3(X20,X21,X22)),X22)
        | ~ r2_hidden(k4_tarski(esk10_3(X20,X21,X22),X31),X20)
        | ~ r2_hidden(k4_tarski(X31,esk11_3(X20,X21,X22)),X21)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk10_3(X20,X21,X22),esk12_3(X20,X21,X22)),X20)
        | r2_hidden(k4_tarski(esk10_3(X20,X21,X22),esk11_3(X20,X21,X22)),X22)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk12_3(X20,X21,X22),esk11_3(X20,X21,X22)),X21)
        | r2_hidden(k4_tarski(esk10_3(X20,X21,X22),esk11_3(X20,X21,X22)),X22)
        | X22 = k5_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_43,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X39)
      | ~ v1_relat_1(X40)
      | v1_relat_1(k5_relat_1(X39,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_44,plain,(
    ! [X70,X71,X72] :
      ( ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      | v1_relat_1(X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk7_0),k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0))
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk5_0)
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0)
    | r2_hidden(k4_tarski(esk6_0,esk7_0),k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(esk9_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(X1,esk9_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk7_0),k5_relat_1(esk4_0,esk5_0))
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk5_0)
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),k5_relat_1(esk4_0,esk5_0))
    | r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(esk9_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_33])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_22])).

cnf(c_0_60,plain,
    ( r2_hidden(k4_tarski(X1,esk9_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk8_0),esk4_0)
    | r2_hidden(k4_tarski(esk6_0,esk7_0),k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk5_0)
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_5(esk4_0,esk5_0,k5_relat_1(esk4_0,esk5_0),esk6_0,esk7_0),esk7_0),esk5_0)
    | r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_55]),c_0_58]),c_0_59])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk9_5(esk4_0,esk5_0,k5_relat_1(esk4_0,esk5_0),esk6_0,esk7_0)),esk4_0)
    | r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_55]),c_0_58]),c_0_59])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),k5_relat_1(esk4_0,esk5_0))
    | r2_hidden(k4_tarski(esk6_0,esk8_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_46])).

cnf(c_0_67,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_62]),c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk8_0),esk4_0)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk5_0)
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_66]),c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_5(esk4_0,esk5_0,k5_relat_1(esk4_0,esk5_0),esk6_0,esk7_0),esk7_0),esk5_0)
    | r2_hidden(k4_tarski(esk6_0,esk8_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_66]),c_0_58]),c_0_59])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk9_5(esk4_0,esk5_0,k5_relat_1(esk4_0,esk5_0),esk6_0,esk7_0)),esk4_0)
    | r2_hidden(k4_tarski(esk6_0,esk8_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_66]),c_0_58]),c_0_59])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),k5_relat_1(X2,esk5_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,esk8_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_58])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk8_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),k5_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_59])])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk7_0),esk5_0)
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_74])]),c_0_56])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_68]),c_0_73])]),
    [proof]).
%------------------------------------------------------------------------------
