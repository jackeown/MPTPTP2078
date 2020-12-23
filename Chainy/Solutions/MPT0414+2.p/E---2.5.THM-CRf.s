%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0414+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:45 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of clauses        :   23 (  25 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 220 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',l3_subset_1)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t6_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d8_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(X1))
                 => ( r2_hidden(X4,X2)
                  <=> r2_hidden(X4,X3) ) )
             => X2 = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_setfam_1])).

fof(c_0_7,negated_conjecture,(
    ! [X1979] :
      ( m1_subset_1(esk107_0,k1_zfmisc_1(k1_zfmisc_1(esk106_0)))
      & m1_subset_1(esk108_0,k1_zfmisc_1(k1_zfmisc_1(esk106_0)))
      & ( ~ r2_hidden(X1979,esk107_0)
        | r2_hidden(X1979,esk108_0)
        | ~ m1_subset_1(X1979,k1_zfmisc_1(esk106_0)) )
      & ( ~ r2_hidden(X1979,esk108_0)
        | r2_hidden(X1979,esk107_0)
        | ~ m1_subset_1(X1979,k1_zfmisc_1(esk106_0)) )
      & esk107_0 != esk108_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_8,plain,(
    ! [X1938,X1939] :
      ( ~ r2_hidden(X1938,X1939)
      | m1_subset_1(X1938,X1939) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_9,plain,(
    ! [X1644,X1645,X1646] :
      ( ~ m1_subset_1(X1645,k1_zfmisc_1(X1644))
      | ~ r2_hidden(X1646,X1645)
      | r2_hidden(X1646,X1644) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(X1,esk108_0)
    | ~ r2_hidden(X1,esk107_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk106_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk107_0,k1_zfmisc_1(k1_zfmisc_1(esk106_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_14,plain,(
    ! [X99,X100] :
      ( ( r2_hidden(esk12_2(X99,X100),X100)
        | ~ r2_xboole_0(X99,X100) )
      & ( ~ r2_hidden(esk12_2(X99,X100),X99)
        | ~ r2_xboole_0(X99,X100) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(X1,esk108_0)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk106_0))
    | ~ r2_hidden(X1,esk107_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk106_0))
    | ~ r2_hidden(X1,esk107_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk107_0)
    | ~ r2_hidden(X1,esk108_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk106_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk108_0,k1_zfmisc_1(k1_zfmisc_1(esk106_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(esk12_2(X1,X2),X1)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk108_0)
    | ~ r2_hidden(X1,esk107_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,esk107_0)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk106_0))
    | ~ r2_hidden(X1,esk108_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk106_0))
    | ~ r2_hidden(X1,esk108_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_18])).

fof(c_0_23,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_xboole_0(esk108_0,X1)
    | ~ r2_hidden(esk12_2(esk108_0,X1),esk107_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(esk12_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_26,plain,(
    ! [X64,X65] :
      ( ( r1_tarski(X64,X65)
        | ~ r2_xboole_0(X64,X65) )
      & ( X64 != X65
        | ~ r2_xboole_0(X64,X65) )
      & ( ~ r1_tarski(X64,X65)
        | X64 = X65
        | r2_xboole_0(X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk107_0)
    | ~ r2_hidden(X1,esk108_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_xboole_0(esk108_0,esk107_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( esk107_0 != esk108_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk108_0,X1)
    | r2_hidden(esk2_2(esk108_0,X1),esk107_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(esk108_0,esk107_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
