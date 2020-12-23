%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t199_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:40 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   27 (  64 expanded)
%              Number of clauses        :   16 (  27 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 242 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t199_funct_2,conjecture,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => m1_funct_2(k1_funct_2(X1,X2),X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',t199_funct_2)).

fof(d13_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ( m1_funct_2(X3,X1,X2)
      <=> ! [X4] :
            ( m1_subset_1(X4,X3)
           => ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',d13_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',t2_subset)).

fof(t121_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',t121_funct_2)).

fof(fc1_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ v1_xboole_0(k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t199_funct_2.p',fc1_funct_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ v1_xboole_0(X2)
       => m1_funct_2(k1_funct_2(X1,X2),X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t199_funct_2])).

fof(c_0_6,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & ~ m1_funct_2(k1_funct_2(esk1_0,esk2_0),esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X9,X10,X11,X12] :
      ( ( v1_funct_1(X12)
        | ~ m1_subset_1(X12,X11)
        | ~ m1_funct_2(X11,X9,X10)
        | v1_xboole_0(X11) )
      & ( v1_funct_2(X12,X9,X10)
        | ~ m1_subset_1(X12,X11)
        | ~ m1_funct_2(X11,X9,X10)
        | v1_xboole_0(X11) )
      & ( m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ m1_subset_1(X12,X11)
        | ~ m1_funct_2(X11,X9,X10)
        | v1_xboole_0(X11) )
      & ( m1_subset_1(esk3_3(X9,X10,X11),X11)
        | m1_funct_2(X11,X9,X10)
        | v1_xboole_0(X11) )
      & ( ~ v1_funct_1(esk3_3(X9,X10,X11))
        | ~ v1_funct_2(esk3_3(X9,X10,X11),X9,X10)
        | ~ m1_subset_1(esk3_3(X9,X10,X11),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | m1_funct_2(X11,X9,X10)
        | v1_xboole_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_funct_2])])])])])])).

fof(c_0_8,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_9,negated_conjecture,
    ( ~ m1_funct_2(k1_funct_2(esk1_0,esk2_0),esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),X3)
    | m1_funct_2(X3,X1,X2)
    | v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X22,X23,X24] :
      ( ( v1_funct_1(X24)
        | ~ r2_hidden(X24,k1_funct_2(X22,X23)) )
      & ( v1_funct_2(X24,X22,X23)
        | ~ r2_hidden(X24,k1_funct_2(X22,X23)) )
      & ( m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ r2_hidden(X24,k1_funct_2(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).

cnf(c_0_12,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_3(esk1_0,esk2_0,k1_funct_2(esk1_0,esk2_0)),k1_funct_2(esk1_0,esk2_0))
    | v1_xboole_0(k1_funct_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_0,esk2_0,k1_funct_2(esk1_0,esk2_0)),k1_funct_2(esk1_0,esk2_0))
    | v1_xboole_0(k1_funct_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_funct_2(X3,X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(esk3_3(X1,X2,X3))
    | ~ v1_funct_2(esk3_3(X1,X2,X3),X1,X2)
    | ~ m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk3_3(esk1_0,esk2_0,k1_funct_2(esk1_0,esk2_0)))
    | v1_xboole_0(k1_funct_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk3_3(esk1_0,esk2_0,k1_funct_2(esk1_0,esk2_0)),esk1_0,esk2_0)
    | v1_xboole_0(k1_funct_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

fof(c_0_20,plain,(
    ! [X42,X43] :
      ( v1_xboole_0(X43)
      | ~ v1_xboole_0(k1_funct_2(X42,X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_funct_2])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v1_xboole_0(k1_funct_2(esk1_0,esk2_0))
    | ~ m1_subset_1(esk3_3(esk1_0,esk2_0,k1_funct_2(esk1_0,esk2_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_9]),c_0_19])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k1_funct_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v1_xboole_0(k1_funct_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
