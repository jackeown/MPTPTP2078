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
% DateTime   : Thu Dec  3 10:46:47 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  106 (1668 expanded)
%              Number of clauses        :   75 ( 768 expanded)
%              Number of leaves         :   15 ( 409 expanded)
%              Depth                    :   18
%              Number of atoms          :  313 (6161 expanded)
%              Number of equality atoms :   29 ( 679 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t44_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(t8_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X48,X49] :
      ( ( ~ m1_subset_1(X49,X48)
        | r2_hidden(X49,X48)
        | v1_xboole_0(X48) )
      & ( ~ r2_hidden(X49,X48)
        | m1_subset_1(X49,X48)
        | v1_xboole_0(X48) )
      & ( ~ m1_subset_1(X49,X48)
        | v1_xboole_0(X49)
        | ~ v1_xboole_0(X48) )
      & ( ~ v1_xboole_0(X49)
        | m1_subset_1(X49,X48)
        | ~ v1_xboole_0(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_17,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X52,X53,X54] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(X52))
      | ~ r2_hidden(X54,X53)
      | r2_hidden(X54,X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_19,negated_conjecture,(
    ! [X68] :
      ( m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))
      & m1_subset_1(esk8_0,k1_zfmisc_1(esk6_0))
      & ( ~ r2_hidden(X68,esk7_0)
        | ~ r2_hidden(X68,esk8_0)
        | ~ m1_subset_1(X68,esk6_0) )
      & ( r2_hidden(X68,esk8_0)
        | r2_hidden(X68,esk7_0)
        | ~ m1_subset_1(X68,esk6_0) )
      & esk7_0 != k3_subset_1(esk6_0,esk8_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_20,plain,(
    ! [X46,X47] : k2_xboole_0(k1_tarski(X46),X47) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | k2_xboole_0(k1_tarski(X44),X45) = X45 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_29,plain,(
    ! [X28,X29,X31,X32,X33] :
      ( ( r2_hidden(esk4_2(X28,X29),X28)
        | r1_xboole_0(X28,X29) )
      & ( r2_hidden(esk4_2(X28,X29),X29)
        | r1_xboole_0(X28,X29) )
      & ( ~ r2_hidden(X33,X31)
        | ~ r2_hidden(X33,X32)
        | ~ r1_xboole_0(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_32,plain,(
    ! [X34,X35] :
      ( ( r1_tarski(X34,X35)
        | X34 != X35 )
      & ( r1_tarski(X35,X34)
        | X34 != X35 )
      & ( ~ r1_tarski(X34,X35)
        | ~ r1_tarski(X35,X34)
        | X34 = X35 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(X50))
      | m1_subset_1(k3_subset_1(X50,X51),k1_zfmisc_1(X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X26,X27] :
      ( ~ r1_xboole_0(X26,X27)
      | r1_xboole_0(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(X1,esk8_0)
    | ~ r2_hidden(esk4_2(X1,esk8_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_34])).

cnf(c_0_48,plain,
    ( v1_xboole_0(k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_50,plain,(
    ! [X36,X37,X38] :
      ( ~ r1_tarski(X36,X37)
      | ~ r1_xboole_0(X37,X38)
      | r1_xboole_0(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_53,plain,(
    ! [X58,X59,X60] :
      ( ( ~ r1_xboole_0(X59,k3_subset_1(X58,X60))
        | r1_tarski(X59,X60)
        | ~ m1_subset_1(X60,k1_zfmisc_1(X58))
        | ~ m1_subset_1(X59,k1_zfmisc_1(X58)) )
      & ( ~ r1_tarski(X59,X60)
        | r1_xboole_0(X59,k3_subset_1(X58,X60))
        | ~ m1_subset_1(X60,k1_zfmisc_1(X58))
        | ~ m1_subset_1(X59,k1_zfmisc_1(X58)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_subset_1])])])])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(k3_subset_1(esk6_0,esk8_0))
    | ~ v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k3_subset_1(esk6_0,esk8_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(X1,esk7_0)
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_49]),c_0_60])])).

cnf(c_0_65,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_42])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(X1,esk8_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0)
    | ~ v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_25])).

fof(c_0_68,plain,(
    ! [X61,X62,X63] :
      ( ( m1_subset_1(esk5_3(X61,X62,X63),X61)
        | X62 = X63
        | ~ m1_subset_1(X63,k1_zfmisc_1(X61))
        | ~ m1_subset_1(X62,k1_zfmisc_1(X61)) )
      & ( ~ r2_hidden(esk5_3(X61,X62,X63),X62)
        | ~ r2_hidden(esk5_3(X61,X62,X63),X63)
        | X62 = X63
        | ~ m1_subset_1(X63,k1_zfmisc_1(X61))
        | ~ m1_subset_1(X62,k1_zfmisc_1(X61)) )
      & ( r2_hidden(esk5_3(X61,X62,X63),X62)
        | r2_hidden(esk5_3(X61,X62,X63),X63)
        | X62 = X63
        | ~ m1_subset_1(X63,k1_zfmisc_1(X61))
        | ~ m1_subset_1(X62,k1_zfmisc_1(X61)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk6_0,esk8_0),k1_zfmisc_1(esk6_0))
    | v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_49])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( esk7_0 != k3_subset_1(esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_72,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_73,plain,(
    ! [X55,X56,X57] :
      ( ( ~ r1_xboole_0(X56,X57)
        | r1_tarski(X56,k3_subset_1(X55,X57))
        | ~ m1_subset_1(X57,k1_zfmisc_1(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(X55)) )
      & ( ~ r1_tarski(X56,k3_subset_1(X55,X57))
        | r1_xboole_0(X56,X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(X55))
        | ~ m1_subset_1(X56,k1_zfmisc_1(X55)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk6_0,esk8_0),k1_zfmisc_1(esk6_0))
    | v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | ~ v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_34])).

cnf(c_0_77,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_59])).

cnf(c_0_78,negated_conjecture,
    ( X1 = esk7_0
    | m1_subset_1(esk5_3(esk6_0,X1,esk7_0),esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_25])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk6_0,k3_subset_1(esk6_0,esk8_0)),k1_zfmisc_1(esk6_0))
    | v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_75])).

cnf(c_0_82,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_76]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk6_0)
    | v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_75]),c_0_71])).

cnf(c_0_85,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_42])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk6_0,k3_subset_1(esk6_0,esk8_0)),k1_zfmisc_1(esk6_0))
    | v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(esk5_3(esk6_0,X1,esk7_0),esk7_0)
    | r2_hidden(esk5_3(esk6_0,X1,esk7_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_25])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk6_0,esk8_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[c_0_75,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | r2_hidden(X1,esk7_0)
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[c_0_84,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk7_0,X1)
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_63])).

cnf(c_0_92,plain,
    ( r1_tarski(k3_subset_1(X1,k3_subset_1(X2,X3)),X3)
    | ~ m1_subset_1(k3_subset_1(X1,k3_subset_1(X2,X3)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk6_0,k3_subset_1(esk6_0,esk8_0)),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[c_0_86,c_0_83])).

cnf(c_0_94,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k3_subset_1(X2,X1))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),k3_subset_1(esk6_0,esk8_0))
    | r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_71])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk8_0)
    | r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk6_0,k3_subset_1(esk6_0,esk8_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_88]),c_0_49])])).

cnf(c_0_99,plain,
    ( X2 = X3
    | ~ r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_49])]),c_0_96])).

cnf(c_0_101,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk7_0,k3_subset_1(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_25]),c_0_88])])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),k3_subset_1(esk6_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_25]),c_0_88])]),c_0_71])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(X1,k3_subset_1(esk6_0,esk8_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.53/0.74  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.53/0.74  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.53/0.74  #
% 0.53/0.74  # Preprocessing time       : 0.029 s
% 0.53/0.74  # Presaturation interreduction done
% 0.53/0.74  
% 0.53/0.74  # Proof found!
% 0.53/0.74  # SZS status Theorem
% 0.53/0.74  # SZS output start CNFRefutation
% 0.53/0.74  fof(t51_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>~(r2_hidden(X4,X3))))=>X2=k3_subset_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_subset_1)).
% 0.53/0.74  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.53/0.74  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.53/0.74  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.53/0.74  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.53/0.74  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.53/0.74  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.53/0.74  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.53/0.74  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.53/0.74  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.53/0.74  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.53/0.74  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.53/0.74  fof(t44_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 0.53/0.74  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 0.53/0.74  fof(t43_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,X3)<=>r1_tarski(X2,k3_subset_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 0.53/0.74  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>~(r2_hidden(X4,X3))))=>X2=k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t51_subset_1])).
% 0.53/0.74  fof(c_0_16, plain, ![X48, X49]:(((~m1_subset_1(X49,X48)|r2_hidden(X49,X48)|v1_xboole_0(X48))&(~r2_hidden(X49,X48)|m1_subset_1(X49,X48)|v1_xboole_0(X48)))&((~m1_subset_1(X49,X48)|v1_xboole_0(X49)|~v1_xboole_0(X48))&(~v1_xboole_0(X49)|m1_subset_1(X49,X48)|~v1_xboole_0(X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.53/0.74  fof(c_0_17, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.53/0.74  fof(c_0_18, plain, ![X52, X53, X54]:(~m1_subset_1(X53,k1_zfmisc_1(X52))|(~r2_hidden(X54,X53)|r2_hidden(X54,X52))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.53/0.74  fof(c_0_19, negated_conjecture, ![X68]:(m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))&(m1_subset_1(esk8_0,k1_zfmisc_1(esk6_0))&(((~r2_hidden(X68,esk7_0)|~r2_hidden(X68,esk8_0)|~m1_subset_1(X68,esk6_0))&(r2_hidden(X68,esk8_0)|r2_hidden(X68,esk7_0)|~m1_subset_1(X68,esk6_0)))&esk7_0!=k3_subset_1(esk6_0,esk8_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.53/0.74  fof(c_0_20, plain, ![X46, X47]:k2_xboole_0(k1_tarski(X46),X47)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.53/0.74  fof(c_0_21, plain, ![X44, X45]:(~r2_hidden(X44,X45)|k2_xboole_0(k1_tarski(X44),X45)=X45), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.53/0.74  cnf(c_0_22, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.53/0.74  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.53/0.74  cnf(c_0_24, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.53/0.74  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.74  cnf(c_0_26, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.53/0.74  cnf(c_0_27, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.53/0.74  fof(c_0_28, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.53/0.74  fof(c_0_29, plain, ![X28, X29, X31, X32, X33]:(((r2_hidden(esk4_2(X28,X29),X28)|r1_xboole_0(X28,X29))&(r2_hidden(esk4_2(X28,X29),X29)|r1_xboole_0(X28,X29)))&(~r2_hidden(X33,X31)|~r2_hidden(X33,X32)|~r1_xboole_0(X31,X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.53/0.74  cnf(c_0_30, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_22, c_0_23])).
% 0.53/0.74  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.53/0.74  fof(c_0_32, plain, ![X34, X35]:(((r1_tarski(X34,X35)|X34!=X35)&(r1_tarski(X35,X34)|X34!=X35))&(~r1_tarski(X34,X35)|~r1_tarski(X35,X34)|X34=X35)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.53/0.74  cnf(c_0_33, plain, (~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])])).
% 0.53/0.74  cnf(c_0_34, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.53/0.74  fof(c_0_35, plain, ![X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(X50))|m1_subset_1(k3_subset_1(X50,X51),k1_zfmisc_1(X50))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.53/0.74  cnf(c_0_36, negated_conjecture, (~r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk8_0)|~m1_subset_1(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.74  cnf(c_0_37, plain, (r2_hidden(esk4_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.74  cnf(c_0_38, negated_conjecture, (m1_subset_1(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.53/0.74  cnf(c_0_39, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.74  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.53/0.74  cnf(c_0_41, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.53/0.74  cnf(c_0_42, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.53/0.74  fof(c_0_43, plain, ![X26, X27]:(~r1_xboole_0(X26,X27)|r1_xboole_0(X27,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.53/0.74  cnf(c_0_44, negated_conjecture, (r1_xboole_0(X1,esk8_0)|~r2_hidden(esk4_2(X1,esk8_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.53/0.74  cnf(c_0_45, plain, (r2_hidden(esk4_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.74  cnf(c_0_46, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.53/0.74  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_34])).
% 0.53/0.74  cnf(c_0_48, plain, (v1_xboole_0(k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.53/0.74  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.74  fof(c_0_50, plain, ![X36, X37, X38]:(~r1_tarski(X36,X37)|~r1_xboole_0(X37,X38)|r1_xboole_0(X36,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.53/0.74  cnf(c_0_51, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.53/0.74  cnf(c_0_52, negated_conjecture, (r1_xboole_0(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.53/0.74  fof(c_0_53, plain, ![X58, X59, X60]:((~r1_xboole_0(X59,k3_subset_1(X58,X60))|r1_tarski(X59,X60)|~m1_subset_1(X60,k1_zfmisc_1(X58))|~m1_subset_1(X59,k1_zfmisc_1(X58)))&(~r1_tarski(X59,X60)|r1_xboole_0(X59,k3_subset_1(X58,X60))|~m1_subset_1(X60,k1_zfmisc_1(X58))|~m1_subset_1(X59,k1_zfmisc_1(X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_subset_1])])])])).
% 0.53/0.74  cnf(c_0_54, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.53/0.74  cnf(c_0_55, negated_conjecture, (v1_xboole_0(k3_subset_1(esk6_0,esk8_0))|~v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.53/0.74  cnf(c_0_56, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.53/0.74  cnf(c_0_57, negated_conjecture, (r1_xboole_0(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.53/0.74  cnf(c_0_58, plain, (r1_tarski(X1,X3)|~r1_xboole_0(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.53/0.74  cnf(c_0_59, negated_conjecture, (k3_subset_1(esk6_0,esk8_0)=k1_xboole_0|~v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.53/0.74  cnf(c_0_60, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_37])).
% 0.53/0.74  cnf(c_0_61, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.53/0.74  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.74  cnf(c_0_63, negated_conjecture, (r1_xboole_0(X1,esk7_0)|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.53/0.74  cnf(c_0_64, negated_conjecture, (r1_tarski(X1,esk8_0)|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))|~v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_49]), c_0_60])])).
% 0.53/0.74  cnf(c_0_65, plain, (r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_42])).
% 0.53/0.74  cnf(c_0_66, negated_conjecture, (~r1_tarski(X1,esk8_0)|~r2_hidden(X2,esk7_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.53/0.74  cnf(c_0_67, negated_conjecture, (r1_tarski(esk7_0,esk8_0)|~v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_64, c_0_25])).
% 0.53/0.74  fof(c_0_68, plain, ![X61, X62, X63]:((m1_subset_1(esk5_3(X61,X62,X63),X61)|X62=X63|~m1_subset_1(X63,k1_zfmisc_1(X61))|~m1_subset_1(X62,k1_zfmisc_1(X61)))&((~r2_hidden(esk5_3(X61,X62,X63),X62)|~r2_hidden(esk5_3(X61,X62,X63),X63)|X62=X63|~m1_subset_1(X63,k1_zfmisc_1(X61))|~m1_subset_1(X62,k1_zfmisc_1(X61)))&(r2_hidden(esk5_3(X61,X62,X63),X62)|r2_hidden(esk5_3(X61,X62,X63),X63)|X62=X63|~m1_subset_1(X63,k1_zfmisc_1(X61))|~m1_subset_1(X62,k1_zfmisc_1(X61))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.53/0.74  cnf(c_0_69, negated_conjecture, (r2_hidden(k3_subset_1(esk6_0,esk8_0),k1_zfmisc_1(esk6_0))|v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_49])).
% 0.53/0.74  cnf(c_0_70, negated_conjecture, (~r2_hidden(X1,esk7_0)|~v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.53/0.74  cnf(c_0_71, negated_conjecture, (esk7_0!=k3_subset_1(esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.74  cnf(c_0_72, plain, (m1_subset_1(esk5_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.53/0.74  fof(c_0_73, plain, ![X55, X56, X57]:((~r1_xboole_0(X56,X57)|r1_tarski(X56,k3_subset_1(X55,X57))|~m1_subset_1(X57,k1_zfmisc_1(X55))|~m1_subset_1(X56,k1_zfmisc_1(X55)))&(~r1_tarski(X56,k3_subset_1(X55,X57))|r1_xboole_0(X56,X57)|~m1_subset_1(X57,k1_zfmisc_1(X55))|~m1_subset_1(X56,k1_zfmisc_1(X55)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).
% 0.53/0.74  cnf(c_0_74, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.74  cnf(c_0_75, negated_conjecture, (m1_subset_1(k3_subset_1(esk6_0,esk8_0),k1_zfmisc_1(esk6_0))|v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_69])).
% 0.53/0.74  cnf(c_0_76, negated_conjecture, (r1_tarski(esk7_0,X1)|~v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_70, c_0_34])).
% 0.53/0.74  cnf(c_0_77, negated_conjecture, (esk7_0!=k1_xboole_0|~v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_71, c_0_59])).
% 0.53/0.74  cnf(c_0_78, negated_conjecture, (X1=esk7_0|m1_subset_1(esk5_3(esk6_0,X1,esk7_0),esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_72, c_0_25])).
% 0.53/0.74  cnf(c_0_79, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.53/0.74  cnf(c_0_80, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_74])).
% 0.53/0.74  cnf(c_0_81, negated_conjecture, (r2_hidden(k3_subset_1(esk6_0,k3_subset_1(esk6_0,esk8_0)),k1_zfmisc_1(esk6_0))|v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_75])).
% 0.53/0.74  cnf(c_0_82, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|r2_hidden(esk5_3(X1,X2,X3),X3)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.53/0.74  cnf(c_0_83, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_76]), c_0_77])).
% 0.53/0.74  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk6_0)|v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_75]), c_0_71])).
% 0.53/0.74  cnf(c_0_85, plain, (r1_xboole_0(k3_subset_1(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_42])).
% 0.53/0.74  cnf(c_0_86, negated_conjecture, (m1_subset_1(k3_subset_1(esk6_0,k3_subset_1(esk6_0,esk8_0)),k1_zfmisc_1(esk6_0))|v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_81])).
% 0.53/0.74  cnf(c_0_87, negated_conjecture, (X1=esk7_0|r2_hidden(esk5_3(esk6_0,X1,esk7_0),esk7_0)|r2_hidden(esk5_3(esk6_0,X1,esk7_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_82, c_0_25])).
% 0.53/0.74  cnf(c_0_88, negated_conjecture, (m1_subset_1(k3_subset_1(esk6_0,esk8_0),k1_zfmisc_1(esk6_0))), inference(sr,[status(thm)],[c_0_75, c_0_83])).
% 0.53/0.74  cnf(c_0_89, negated_conjecture, (r2_hidden(X1,esk8_0)|r2_hidden(X1,esk7_0)|~m1_subset_1(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.74  cnf(c_0_90, negated_conjecture, (m1_subset_1(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk6_0)), inference(sr,[status(thm)],[c_0_84, c_0_83])).
% 0.53/0.74  cnf(c_0_91, negated_conjecture, (r1_xboole_0(esk7_0,X1)|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_63])).
% 0.53/0.74  cnf(c_0_92, plain, (r1_tarski(k3_subset_1(X1,k3_subset_1(X2,X3)),X3)|~m1_subset_1(k3_subset_1(X1,k3_subset_1(X2,X3)),k1_zfmisc_1(X2))|~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_58, c_0_85])).
% 0.53/0.74  cnf(c_0_93, negated_conjecture, (m1_subset_1(k3_subset_1(esk6_0,k3_subset_1(esk6_0,esk8_0)),k1_zfmisc_1(esk6_0))), inference(sr,[status(thm)],[c_0_86, c_0_83])).
% 0.53/0.74  cnf(c_0_94, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k3_subset_1(X2,X1))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_62, c_0_85])).
% 0.53/0.74  cnf(c_0_95, negated_conjecture, (r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),k3_subset_1(esk6_0,esk8_0))|r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_71])).
% 0.53/0.74  cnf(c_0_96, negated_conjecture, (r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk8_0)|r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.53/0.74  cnf(c_0_97, negated_conjecture, (r1_tarski(esk7_0,X1)|~m1_subset_1(esk7_0,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(k3_subset_1(X2,X1),esk8_0)), inference(spm,[status(thm)],[c_0_58, c_0_91])).
% 0.53/0.74  cnf(c_0_98, negated_conjecture, (r1_tarski(k3_subset_1(esk6_0,k3_subset_1(esk6_0,esk8_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_88]), c_0_49])])).
% 0.53/0.74  cnf(c_0_99, plain, (X2=X3|~r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(esk5_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.53/0.74  cnf(c_0_100, negated_conjecture, (r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_49])]), c_0_96])).
% 0.53/0.74  cnf(c_0_101, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.53/0.74  cnf(c_0_102, negated_conjecture, (r1_tarski(esk7_0,k3_subset_1(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_25]), c_0_88])])).
% 0.53/0.74  cnf(c_0_103, negated_conjecture, (~r2_hidden(esk5_3(esk6_0,k3_subset_1(esk6_0,esk8_0),esk7_0),k3_subset_1(esk6_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_25]), c_0_88])]), c_0_71])).
% 0.53/0.74  cnf(c_0_104, negated_conjecture, (r2_hidden(X1,k3_subset_1(esk6_0,esk8_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.53/0.74  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_100])]), ['proof']).
% 0.53/0.74  # SZS output end CNFRefutation
% 0.53/0.74  # Proof object total steps             : 106
% 0.53/0.74  # Proof object clause steps            : 75
% 0.53/0.74  # Proof object formula steps           : 31
% 0.53/0.74  # Proof object conjectures             : 43
% 0.53/0.74  # Proof object clause conjectures      : 40
% 0.53/0.74  # Proof object formula conjectures     : 3
% 0.53/0.74  # Proof object initial clauses used    : 27
% 0.53/0.74  # Proof object initial formulas used   : 15
% 0.53/0.74  # Proof object generating inferences   : 43
% 0.53/0.74  # Proof object simplifying inferences  : 29
% 0.53/0.74  # Training examples: 0 positive, 0 negative
% 0.53/0.74  # Parsed axioms                        : 19
% 0.53/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.74  # Initial clauses                      : 45
% 0.53/0.74  # Removed in clause preprocessing      : 0
% 0.53/0.74  # Initial clauses in saturation        : 45
% 0.53/0.74  # Processed clauses                    : 6106
% 0.53/0.74  # ...of these trivial                  : 54
% 0.53/0.74  # ...subsumed                          : 4682
% 0.53/0.74  # ...remaining for further processing  : 1370
% 0.53/0.74  # Other redundant clauses eliminated   : 8
% 0.53/0.74  # Clauses deleted for lack of memory   : 0
% 0.53/0.74  # Backward-subsumed                    : 56
% 0.53/0.74  # Backward-rewritten                   : 20
% 0.53/0.74  # Generated clauses                    : 32552
% 0.53/0.74  # ...of the previous two non-trivial   : 27779
% 0.53/0.74  # Contextual simplify-reflections      : 37
% 0.53/0.74  # Paramodulations                      : 32456
% 0.53/0.74  # Factorizations                       : 36
% 0.53/0.74  # Equation resolutions                 : 8
% 0.53/0.74  # Propositional unsat checks           : 0
% 0.53/0.74  #    Propositional check models        : 0
% 0.53/0.74  #    Propositional check unsatisfiable : 0
% 0.53/0.74  #    Propositional clauses             : 0
% 0.53/0.74  #    Propositional clauses after purity: 0
% 0.53/0.74  #    Propositional unsat core size     : 0
% 0.53/0.74  #    Propositional preprocessing time  : 0.000
% 0.53/0.74  #    Propositional encoding time       : 0.000
% 0.53/0.74  #    Propositional solver time         : 0.000
% 0.53/0.74  #    Success case prop preproc time    : 0.000
% 0.53/0.74  #    Success case prop encoding time   : 0.000
% 0.53/0.74  #    Success case prop solver time     : 0.000
% 0.53/0.74  # Current number of processed clauses  : 1193
% 0.53/0.74  #    Positive orientable unit clauses  : 120
% 0.53/0.74  #    Positive unorientable unit clauses: 0
% 0.53/0.74  #    Negative unit clauses             : 15
% 0.53/0.74  #    Non-unit-clauses                  : 1058
% 0.53/0.74  # Current number of unprocessed clauses: 21426
% 0.53/0.74  # ...number of literals in the above   : 73107
% 0.53/0.74  # Current number of archived formulas  : 0
% 0.53/0.74  # Current number of archived clauses   : 172
% 0.53/0.74  # Clause-clause subsumption calls (NU) : 153924
% 0.53/0.74  # Rec. Clause-clause subsumption calls : 104736
% 0.53/0.74  # Non-unit clause-clause subsumptions  : 1929
% 0.53/0.74  # Unit Clause-clause subsumption calls : 12041
% 0.53/0.74  # Rewrite failures with RHS unbound    : 0
% 0.53/0.74  # BW rewrite match attempts            : 701
% 0.53/0.74  # BW rewrite match successes           : 22
% 0.53/0.74  # Condensation attempts                : 0
% 0.53/0.74  # Condensation successes               : 0
% 0.53/0.74  # Termbank termtop insertions          : 535572
% 0.53/0.74  
% 0.53/0.74  # -------------------------------------------------
% 0.53/0.74  # User time                : 0.393 s
% 0.53/0.74  # System time              : 0.016 s
% 0.53/0.74  # Total time               : 0.409 s
% 0.53/0.74  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
