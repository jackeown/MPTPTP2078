%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0418+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  87 expanded)
%              Number of clauses        :   18 (  33 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 348 expanded)
%              Number of equality atoms :   11 (  30 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(t49_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
          <=> r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',dt_k3_subset_1)).

fof(c_0_6,plain,(
    ! [X1918,X1919,X1920,X1921] :
      ( ( ~ r2_hidden(X1921,X1920)
        | r2_hidden(k3_subset_1(X1918,X1921),X1919)
        | ~ m1_subset_1(X1921,k1_zfmisc_1(X1918))
        | X1920 != k7_setfam_1(X1918,X1919)
        | ~ m1_subset_1(X1920,k1_zfmisc_1(k1_zfmisc_1(X1918)))
        | ~ m1_subset_1(X1919,k1_zfmisc_1(k1_zfmisc_1(X1918))) )
      & ( ~ r2_hidden(k3_subset_1(X1918,X1921),X1919)
        | r2_hidden(X1921,X1920)
        | ~ m1_subset_1(X1921,k1_zfmisc_1(X1918))
        | X1920 != k7_setfam_1(X1918,X1919)
        | ~ m1_subset_1(X1920,k1_zfmisc_1(k1_zfmisc_1(X1918)))
        | ~ m1_subset_1(X1919,k1_zfmisc_1(k1_zfmisc_1(X1918))) )
      & ( m1_subset_1(esk104_3(X1918,X1919,X1920),k1_zfmisc_1(X1918))
        | X1920 = k7_setfam_1(X1918,X1919)
        | ~ m1_subset_1(X1920,k1_zfmisc_1(k1_zfmisc_1(X1918)))
        | ~ m1_subset_1(X1919,k1_zfmisc_1(k1_zfmisc_1(X1918))) )
      & ( ~ r2_hidden(esk104_3(X1918,X1919,X1920),X1920)
        | ~ r2_hidden(k3_subset_1(X1918,esk104_3(X1918,X1919,X1920)),X1919)
        | X1920 = k7_setfam_1(X1918,X1919)
        | ~ m1_subset_1(X1920,k1_zfmisc_1(k1_zfmisc_1(X1918)))
        | ~ m1_subset_1(X1919,k1_zfmisc_1(k1_zfmisc_1(X1918))) )
      & ( r2_hidden(esk104_3(X1918,X1919,X1920),X1920)
        | r2_hidden(k3_subset_1(X1918,esk104_3(X1918,X1919,X1920)),X1919)
        | X1920 = k7_setfam_1(X1918,X1919)
        | ~ m1_subset_1(X1920,k1_zfmisc_1(k1_zfmisc_1(X1918)))
        | ~ m1_subset_1(X1919,k1_zfmisc_1(k1_zfmisc_1(X1918))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_7,plain,(
    ! [X2011,X2012,X2013] :
      ( ~ r2_hidden(X2011,X2012)
      | ~ m1_subset_1(X2012,k1_zfmisc_1(X2013))
      | m1_subset_1(X2011,X2013) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_8,plain,(
    ! [X1927,X1928] :
      ( ~ m1_subset_1(X1928,k1_zfmisc_1(k1_zfmisc_1(X1927)))
      | m1_subset_1(k7_setfam_1(X1927,X1928),k1_zfmisc_1(k1_zfmisc_1(X1927))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
            <=> r2_hidden(X3,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_setfam_1])).

cnf(c_0_10,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk109_0,k1_zfmisc_1(k1_zfmisc_1(esk108_0)))
    & m1_subset_1(esk110_0,k1_zfmisc_1(esk108_0))
    & ( ~ r2_hidden(k3_subset_1(esk108_0,esk110_0),k7_setfam_1(esk108_0,esk109_0))
      | ~ r2_hidden(esk110_0,esk109_0) )
    & ( r2_hidden(k3_subset_1(esk108_0,esk110_0),k7_setfam_1(esk108_0,esk109_0))
      | r2_hidden(esk110_0,esk109_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_10,c_0_11])]),c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk108_0,esk110_0),k7_setfam_1(esk108_0,esk109_0))
    | r2_hidden(esk110_0,esk109_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk109_0,k1_zfmisc_1(k1_zfmisc_1(esk108_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X1642,X1643] :
      ( ~ m1_subset_1(X1643,k1_zfmisc_1(X1642))
      | k3_subset_1(X1642,k3_subset_1(X1642,X1643)) = X1643 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk108_0,k3_subset_1(esk108_0,esk110_0)),esk109_0)
    | r2_hidden(esk110_0,esk109_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_19,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk110_0,k1_zfmisc_1(esk108_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk108_0,esk110_0),k7_setfam_1(esk108_0,esk109_0))
    | ~ r2_hidden(esk110_0,esk109_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk110_0,esk109_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_23,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk108_0,esk110_0),k7_setfam_1(esk108_0,esk109_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_subset_1(k3_subset_1(esk108_0,esk110_0),k1_zfmisc_1(esk108_0))
    | ~ r2_hidden(k3_subset_1(esk108_0,k3_subset_1(esk108_0,esk110_0)),esk109_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_16])])).

fof(c_0_27,plain,(
    ! [X1576,X1577] :
      ( ~ m1_subset_1(X1577,k1_zfmisc_1(X1576))
      | m1_subset_1(k3_subset_1(X1576,X1577),k1_zfmisc_1(X1576)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(k3_subset_1(esk108_0,esk110_0),k1_zfmisc_1(esk108_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_22]),c_0_20])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
