%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0415+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:45 EST 2020

% Result     : Theorem 1.35s
% Output     : CNFRefutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   52 (  76 expanded)
%              Number of clauses        :   25 (  33 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  131 ( 176 expanded)
%              Number of equality atoms :   47 (  78 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t113_zfmisc_1)).

fof(t46_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',d3_subset_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',dt_k1_subset_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t152_zfmisc_1)).

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

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(t50_subset_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ( ~ r2_hidden(X3,X2)
               => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',t50_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',existence_m1_subset_1)).

fof(c_0_13,plain,(
    ! [X1139,X1140] :
      ( ( k2_zfmisc_1(X1139,X1140) != k1_xboole_0
        | X1139 = k1_xboole_0
        | X1140 = k1_xboole_0 )
      & ( X1139 != k1_xboole_0
        | k2_zfmisc_1(X1139,X1140) = k1_xboole_0 )
      & ( X1140 != k1_xboole_0
        | k2_zfmisc_1(X1139,X1140) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t46_setfam_1])).

fof(c_0_15,plain,(
    ! [X1691] : k2_subset_1(X1691) = k3_subset_1(X1691,k1_subset_1(X1691)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_16,plain,(
    ! [X1531] : k2_subset_1(X1531) = X1531 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_17,plain,(
    ! [X1513] : k1_subset_1(X1513) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_18,plain,(
    ! [X1574] : m1_subset_1(k1_subset_1(X1574),k1_zfmisc_1(X1574)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_19,plain,(
    ! [X1272,X1273] : ~ r2_hidden(X1272,k2_zfmisc_1(X1272,X1273)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
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

fof(c_0_22,plain,(
    ! [X1995,X1996,X1997] :
      ( ~ r2_hidden(X1995,X1996)
      | ~ m1_subset_1(X1996,k1_zfmisc_1(X1997))
      | m1_subset_1(X1995,X1997) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_23,plain,(
    ! [X1923,X1924] :
      ( ~ m1_subset_1(X1924,k1_zfmisc_1(k1_zfmisc_1(X1923)))
      | m1_subset_1(k7_setfam_1(X1923,X1924),k1_zfmisc_1(k1_zfmisc_1(X1923))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_24,plain,(
    ! [X1930,X1931] :
      ( ~ m1_subset_1(X1931,k1_zfmisc_1(k1_zfmisc_1(X1930)))
      | k7_setfam_1(X1930,k7_setfam_1(X1930,X1931)) = X1931 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_25,negated_conjecture,
    ( m1_subset_1(esk109_0,k1_zfmisc_1(k1_zfmisc_1(esk108_0)))
    & esk109_0 != k1_xboole_0
    & k7_setfam_1(esk108_0,esk109_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_26,plain,(
    ! [X1748,X1749,X1750] :
      ( X1748 = k1_xboole_0
      | ~ m1_subset_1(X1749,k1_zfmisc_1(X1748))
      | ~ m1_subset_1(X1750,X1748)
      | r2_hidden(X1750,X1749)
      | r2_hidden(X1750,k3_subset_1(X1748,X1749)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_subset_1])])])])).

cnf(c_0_27,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( k7_setfam_1(esk108_0,esk109_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk109_0,k1_zfmisc_1(k1_zfmisc_1(esk108_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,X2)
    | r2_hidden(X3,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_43,plain,(
    ! [X1595] : m1_subset_1(esk65_1(X1595),X1595) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_44,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_33,c_0_34])]),c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k7_setfam_1(esk108_0,k1_xboole_0) = esk109_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk65_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(X1,esk109_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_41])]),c_0_42])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk65_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( esk109_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
