%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t51_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:24 EDT 2019

% Result     : Theorem 1.05s
% Output     : CNFRefutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 195 expanded)
%              Number of clauses        :   25 (  86 expanded)
%              Number of leaves         :    6 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 900 expanded)
%              Number of equality atoms :   24 ( 167 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> ~ r2_hidden(X4,X3) ) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t51_subset_1.p',t51_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t51_subset_1.p',l3_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t51_subset_1.p',d5_xboole_0)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t51_subset_1.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t51_subset_1.p',t7_boole)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t51_subset_1.p',d5_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( r2_hidden(X4,X2)
                  <=> ~ r2_hidden(X4,X3) ) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_subset_1])).

fof(c_0_7,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | ~ r2_hidden(X47,X46)
      | r2_hidden(X47,X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_8,negated_conjecture,(
    ! [X8] :
      ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
      & ( ~ r2_hidden(X8,esk2_0)
        | ~ r2_hidden(X8,esk3_0)
        | ~ m1_subset_1(X8,esk1_0) )
      & ( r2_hidden(X8,esk3_0)
        | r2_hidden(X8,esk2_0)
        | ~ m1_subset_1(X8,esk1_0) )
      & esk2_0 != k3_subset_1(esk1_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( r2_hidden(X33,X30)
        | ~ r2_hidden(X33,X32)
        | X32 != k4_xboole_0(X30,X31) )
      & ( ~ r2_hidden(X33,X31)
        | ~ r2_hidden(X33,X32)
        | X32 != k4_xboole_0(X30,X31) )
      & ( ~ r2_hidden(X34,X30)
        | r2_hidden(X34,X31)
        | r2_hidden(X34,X32)
        | X32 != k4_xboole_0(X30,X31) )
      & ( ~ r2_hidden(esk6_3(X35,X36,X37),X37)
        | ~ r2_hidden(esk6_3(X35,X36,X37),X35)
        | r2_hidden(esk6_3(X35,X36,X37),X36)
        | X37 = k4_xboole_0(X35,X36) )
      & ( r2_hidden(esk6_3(X35,X36,X37),X35)
        | r2_hidden(esk6_3(X35,X36,X37),X37)
        | X37 = k4_xboole_0(X35,X36) )
      & ( ~ r2_hidden(esk6_3(X35,X36,X37),X36)
        | r2_hidden(esk6_3(X35,X36,X37),X37)
        | X37 = k4_xboole_0(X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_12,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X21,X20)
        | r2_hidden(X21,X20)
        | v1_xboole_0(X20) )
      & ( ~ r2_hidden(X21,X20)
        | m1_subset_1(X21,X20)
        | v1_xboole_0(X20) )
      & ( ~ m1_subset_1(X21,X20)
        | v1_xboole_0(X21)
        | ~ v1_xboole_0(X20) )
      & ( ~ v1_xboole_0(X21)
        | m1_subset_1(X21,X20)
        | ~ v1_xboole_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_13,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | ~ v1_xboole_0(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k4_xboole_0(X1,X2) = esk2_0
    | r2_hidden(esk6_3(X1,X2,esk2_0),esk1_0)
    | r2_hidden(esk6_3(X1,X2,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | k3_subset_1(X28,X29) = k4_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k4_xboole_0(esk1_0,X1) = esk2_0
    | r2_hidden(esk6_3(esk1_0,X1,esk2_0),esk1_0) ),
    inference(ef,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(esk1_0,X1) = esk2_0
    | m1_subset_1(esk6_3(esk1_0,X1,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 != k3_subset_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( k3_subset_1(esk1_0,esk3_0) = k4_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(esk1_0,X1) = esk2_0
    | r2_hidden(esk6_3(esk1_0,X1,esk2_0),esk2_0)
    | r2_hidden(esk6_3(esk1_0,X1,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(esk1_0,X1) = esk2_0
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk2_0),esk2_0)
    | ~ r2_hidden(esk6_3(esk1_0,X1,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_34,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,esk3_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk6_3(esk1_0,esk3_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_30]),c_0_35])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
