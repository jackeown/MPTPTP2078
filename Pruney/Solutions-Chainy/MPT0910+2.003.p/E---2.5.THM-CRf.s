%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:11 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 311 expanded)
%              Number of clauses        :   55 ( 136 expanded)
%              Number of leaves         :   15 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  229 (1281 expanded)
%              Number of equality atoms :  108 ( 765 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t70_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X7 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_15,plain,(
    ! [X30,X31] :
      ( ( k2_zfmisc_1(X30,X31) != k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0 )
      & ( X30 != k1_xboole_0
        | k2_zfmisc_1(X30,X31) = k1_xboole_0 )
      & ( X31 != k1_xboole_0
        | k2_zfmisc_1(X30,X31) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X32,X33] : ~ r2_hidden(X32,k2_zfmisc_1(X32,X33)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X7 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_mcart_1])).

fof(c_0_19,plain,(
    ! [X13,X14] :
      ( ( ~ r2_hidden(esk2_2(X13,X14),X13)
        | ~ r2_hidden(esk2_2(X13,X14),X14)
        | X13 = X14 )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r2_hidden(esk2_2(X13,X14),X14)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,(
    ! [X78,X79,X80] :
      ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X78,esk4_0)
        | ~ m1_subset_1(X79,esk5_0)
        | ~ m1_subset_1(X80,esk6_0)
        | esk8_0 != k3_mcart_1(X78,X79,X80)
        | esk7_0 = X79 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])).

fof(c_0_23,plain,(
    ! [X41,X42,X43] : k3_zfmisc_1(X41,X42,X43) = k2_zfmisc_1(k2_zfmisc_1(X41,X42),X43) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X34,X35)
      | v1_xboole_0(X35)
      | r2_hidden(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25])]),c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(X1,esk5_0)),k2_zfmisc_1(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(esk4_0,esk5_0)),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_43,plain,(
    ! [X65,X66,X67,X68] :
      ( ( k5_mcart_1(X65,X66,X67,X68) = k1_mcart_1(k1_mcart_1(X68))
        | ~ m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0 )
      & ( k6_mcart_1(X65,X66,X67,X68) = k2_mcart_1(k1_mcart_1(X68))
        | ~ m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0 )
      & ( k7_mcart_1(X65,X66,X67,X68) = k2_mcart_1(X68)
        | ~ m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_44,plain,(
    ! [X63,X64] :
      ( ~ v1_relat_1(X64)
      | ~ r2_hidden(X63,X64)
      | X63 = k4_tarski(k1_mcart_1(X63),k2_mcart_1(X63)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_45,plain,(
    ! [X36,X37] : v1_relat_1(k2_zfmisc_1(X36,X37)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_46,plain,(
    ! [X60,X61,X62] :
      ( ( r2_hidden(k1_mcart_1(X60),X61)
        | ~ r2_hidden(X60,k2_zfmisc_1(X61,X62)) )
      & ( r2_hidden(k2_mcart_1(X60),X62)
        | ~ r2_hidden(X60,k2_zfmisc_1(X61,X62)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ m1_subset_1(X55,k3_zfmisc_1(X52,X53,X54))
      | m1_subset_1(k6_mcart_1(X52,X53,X54,X55),X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

fof(c_0_52,plain,(
    ! [X48,X49,X50,X51] :
      ( ~ m1_subset_1(X51,k3_zfmisc_1(X48,X49,X50))
      | m1_subset_1(k5_mcart_1(X48,X49,X50,X51),X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

fof(c_0_53,plain,(
    ! [X56,X57,X58,X59] :
      ( ~ m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))
      | m1_subset_1(k7_mcart_1(X56,X57,X58,X59),X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

fof(c_0_54,plain,(
    ! [X38,X39,X40] : k3_mcart_1(X38,X39,X40) = k4_tarski(k4_tarski(X38,X39),X40) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_55,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_29])).

cnf(c_0_60,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_61,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_65,negated_conjecture,
    ( esk7_0 = X2
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X3,esk6_0)
    | esk8_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_66,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk8_0)) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_35]),c_0_30]),c_0_32]),c_0_37])).

cnf(c_0_70,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk8_0)) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_35]),c_0_30]),c_0_32]),c_0_37])).

cnf(c_0_71,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_29])).

cnf(c_0_72,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_29])).

cnf(c_0_73,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_29])).

cnf(c_0_74,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_29])).

cnf(c_0_75,negated_conjecture,
    ( esk7_0 = X2
    | esk8_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk6_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)) = k1_mcart_1(esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_35])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_35])).

cnf(c_0_79,negated_conjecture,
    ( esk7_0 != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_35])).

cnf(c_0_81,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) = k2_mcart_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_35]),c_0_30]),c_0_32]),c_0_37])).

cnf(c_0_82,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),X1) != esk8_0
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78])]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_58])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk8_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:27:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.60/3.84  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 3.60/3.84  # and selection function SelectNegativeLiterals.
% 3.60/3.84  #
% 3.60/3.84  # Preprocessing time       : 0.029 s
% 3.60/3.84  # Presaturation interreduction done
% 3.60/3.84  
% 3.60/3.84  # Proof found!
% 3.60/3.84  # SZS status Theorem
% 3.60/3.84  # SZS output start CNFRefutation
% 3.60/3.84  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.60/3.84  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.60/3.84  fof(t70_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_mcart_1)).
% 3.60/3.84  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.60/3.84  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.60/3.84  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.60/3.84  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.60/3.84  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.60/3.84  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 3.60/3.84  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.60/3.84  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.60/3.84  fof(dt_k6_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 3.60/3.84  fof(dt_k5_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 3.60/3.84  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 3.60/3.84  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.60/3.84  fof(c_0_15, plain, ![X30, X31]:((k2_zfmisc_1(X30,X31)!=k1_xboole_0|(X30=k1_xboole_0|X31=k1_xboole_0))&((X30!=k1_xboole_0|k2_zfmisc_1(X30,X31)=k1_xboole_0)&(X31!=k1_xboole_0|k2_zfmisc_1(X30,X31)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 3.60/3.84  fof(c_0_16, plain, ![X32, X33]:~r2_hidden(X32,k2_zfmisc_1(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 3.60/3.84  cnf(c_0_17, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.60/3.84  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t70_mcart_1])).
% 3.60/3.84  fof(c_0_19, plain, ![X13, X14]:((~r2_hidden(esk2_2(X13,X14),X13)|~r2_hidden(esk2_2(X13,X14),X14)|X13=X14)&(r2_hidden(esk2_2(X13,X14),X13)|r2_hidden(esk2_2(X13,X14),X14)|X13=X14)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 3.60/3.84  cnf(c_0_20, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.60/3.84  cnf(c_0_21, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_17])).
% 3.60/3.84  fof(c_0_22, negated_conjecture, ![X78, X79, X80]:(m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X78,esk4_0)|(~m1_subset_1(X79,esk5_0)|(~m1_subset_1(X80,esk6_0)|(esk8_0!=k3_mcart_1(X78,X79,X80)|esk7_0=X79))))&(((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])).
% 3.60/3.84  fof(c_0_23, plain, ![X41, X42, X43]:k3_zfmisc_1(X41,X42,X43)=k2_zfmisc_1(k2_zfmisc_1(X41,X42),X43), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 3.60/3.84  cnf(c_0_24, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.60/3.84  cnf(c_0_25, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.60/3.84  cnf(c_0_26, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 3.60/3.84  fof(c_0_27, plain, ![X34, X35]:(~m1_subset_1(X34,X35)|(v1_xboole_0(X35)|r2_hidden(X34,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 3.60/3.84  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.60/3.84  cnf(c_0_29, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.60/3.84  cnf(c_0_30, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.60/3.84  cnf(c_0_31, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25])]), c_0_26])).
% 3.60/3.84  cnf(c_0_32, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.60/3.84  fof(c_0_33, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 3.60/3.84  cnf(c_0_34, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.60/3.84  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 3.60/3.84  cnf(c_0_36, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 3.60/3.84  cnf(c_0_37, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.60/3.84  cnf(c_0_38, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(X1,esk5_0)),k2_zfmisc_1(X1,esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 3.60/3.84  cnf(c_0_39, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.60/3.84  cnf(c_0_40, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 3.60/3.84  cnf(c_0_41, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 3.60/3.84  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(esk4_0,esk5_0)),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.60/3.84  fof(c_0_43, plain, ![X65, X66, X67, X68]:(((k5_mcart_1(X65,X66,X67,X68)=k1_mcart_1(k1_mcart_1(X68))|~m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))|(X65=k1_xboole_0|X66=k1_xboole_0|X67=k1_xboole_0))&(k6_mcart_1(X65,X66,X67,X68)=k2_mcart_1(k1_mcart_1(X68))|~m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))|(X65=k1_xboole_0|X66=k1_xboole_0|X67=k1_xboole_0)))&(k7_mcart_1(X65,X66,X67,X68)=k2_mcart_1(X68)|~m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))|(X65=k1_xboole_0|X66=k1_xboole_0|X67=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 3.60/3.84  fof(c_0_44, plain, ![X63, X64]:(~v1_relat_1(X64)|(~r2_hidden(X63,X64)|X63=k4_tarski(k1_mcart_1(X63),k2_mcart_1(X63)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 3.60/3.84  fof(c_0_45, plain, ![X36, X37]:v1_relat_1(k2_zfmisc_1(X36,X37)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 3.60/3.84  fof(c_0_46, plain, ![X60, X61, X62]:((r2_hidden(k1_mcart_1(X60),X61)|~r2_hidden(X60,k2_zfmisc_1(X61,X62)))&(r2_hidden(k2_mcart_1(X60),X62)|~r2_hidden(X60,k2_zfmisc_1(X61,X62)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 3.60/3.84  cnf(c_0_47, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 3.60/3.84  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 3.60/3.84  cnf(c_0_49, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.60/3.84  cnf(c_0_50, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.60/3.84  fof(c_0_51, plain, ![X52, X53, X54, X55]:(~m1_subset_1(X55,k3_zfmisc_1(X52,X53,X54))|m1_subset_1(k6_mcart_1(X52,X53,X54,X55),X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).
% 3.60/3.84  fof(c_0_52, plain, ![X48, X49, X50, X51]:(~m1_subset_1(X51,k3_zfmisc_1(X48,X49,X50))|m1_subset_1(k5_mcart_1(X48,X49,X50,X51),X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).
% 3.60/3.84  fof(c_0_53, plain, ![X56, X57, X58, X59]:(~m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))|m1_subset_1(k7_mcart_1(X56,X57,X58,X59),X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 3.60/3.84  fof(c_0_54, plain, ![X38, X39, X40]:k3_mcart_1(X38,X39,X40)=k4_tarski(k4_tarski(X38,X39),X40), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 3.60/3.84  cnf(c_0_55, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 3.60/3.84  cnf(c_0_56, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.60/3.84  cnf(c_0_57, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.60/3.84  cnf(c_0_58, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 3.60/3.84  cnf(c_0_59, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_49, c_0_29])).
% 3.60/3.84  cnf(c_0_60, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_50, c_0_29])).
% 3.60/3.84  cnf(c_0_61, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 3.60/3.84  cnf(c_0_62, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 3.60/3.84  cnf(c_0_63, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 3.60/3.84  cnf(c_0_64, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.60/3.84  cnf(c_0_65, negated_conjecture, (esk7_0=X2|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X3,esk6_0)|esk8_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.60/3.84  cnf(c_0_66, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.60/3.84  cnf(c_0_67, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 3.60/3.84  cnf(c_0_68, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 3.60/3.84  cnf(c_0_69, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk8_0))=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_35]), c_0_30]), c_0_32]), c_0_37])).
% 3.60/3.84  cnf(c_0_70, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk8_0))=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_35]), c_0_30]), c_0_32]), c_0_37])).
% 3.60/3.84  cnf(c_0_71, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_61, c_0_29])).
% 3.60/3.84  cnf(c_0_72, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_62, c_0_29])).
% 3.60/3.84  cnf(c_0_73, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_63, c_0_29])).
% 3.60/3.84  cnf(c_0_74, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_64, c_0_29])).
% 3.60/3.84  cnf(c_0_75, negated_conjecture, (esk7_0=X2|esk8_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk6_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 3.60/3.84  cnf(c_0_76, negated_conjecture, (k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0))=k1_mcart_1(esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70])).
% 3.60/3.84  cnf(c_0_77, negated_conjecture, (m1_subset_1(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_35])).
% 3.60/3.84  cnf(c_0_78, negated_conjecture, (m1_subset_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0)), inference(spm,[status(thm)],[c_0_72, c_0_35])).
% 3.60/3.84  cnf(c_0_79, negated_conjecture, (esk7_0!=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.60/3.84  cnf(c_0_80, negated_conjecture, (m1_subset_1(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_73, c_0_35])).
% 3.60/3.84  cnf(c_0_81, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)=k2_mcart_1(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_35]), c_0_30]), c_0_32]), c_0_37])).
% 3.60/3.84  cnf(c_0_82, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),X1)!=esk8_0|~m1_subset_1(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78])]), c_0_79])).
% 3.60/3.84  cnf(c_0_83, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0))=esk8_0), inference(spm,[status(thm)],[c_0_67, c_0_58])).
% 3.60/3.84  cnf(c_0_84, negated_conjecture, (m1_subset_1(k2_mcart_1(esk8_0),esk6_0)), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 3.60/3.84  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])]), ['proof']).
% 3.60/3.84  # SZS output end CNFRefutation
% 3.60/3.84  # Proof object total steps             : 86
% 3.60/3.84  # Proof object clause steps            : 55
% 3.60/3.84  # Proof object formula steps           : 31
% 3.60/3.84  # Proof object conjectures             : 31
% 3.60/3.84  # Proof object clause conjectures      : 28
% 3.60/3.84  # Proof object formula conjectures     : 3
% 3.60/3.84  # Proof object initial clauses used    : 23
% 3.60/3.84  # Proof object initial formulas used   : 15
% 3.60/3.84  # Proof object generating inferences   : 22
% 3.60/3.84  # Proof object simplifying inferences  : 29
% 3.60/3.84  # Training examples: 0 positive, 0 negative
% 3.60/3.84  # Parsed axioms                        : 20
% 3.60/3.84  # Removed by relevancy pruning/SinE    : 0
% 3.60/3.84  # Initial clauses                      : 41
% 3.60/3.84  # Removed in clause preprocessing      : 5
% 3.60/3.84  # Initial clauses in saturation        : 36
% 3.60/3.84  # Processed clauses                    : 12587
% 3.60/3.84  # ...of these trivial                  : 2384
% 3.60/3.84  # ...subsumed                          : 8692
% 3.60/3.84  # ...remaining for further processing  : 1511
% 3.60/3.84  # Other redundant clauses eliminated   : 7529
% 3.60/3.84  # Clauses deleted for lack of memory   : 0
% 3.60/3.84  # Backward-subsumed                    : 4
% 3.60/3.84  # Backward-rewritten                   : 203
% 3.60/3.84  # Generated clauses                    : 576650
% 3.60/3.84  # ...of the previous two non-trivial   : 455278
% 3.60/3.84  # Contextual simplify-reflections      : 16
% 3.60/3.84  # Paramodulations                      : 568727
% 3.60/3.84  # Factorizations                       : 396
% 3.60/3.84  # Equation resolutions                 : 7529
% 3.60/3.84  # Propositional unsat checks           : 0
% 3.60/3.84  #    Propositional check models        : 0
% 3.60/3.84  #    Propositional check unsatisfiable : 0
% 3.60/3.84  #    Propositional clauses             : 0
% 3.60/3.84  #    Propositional clauses after purity: 0
% 3.60/3.84  #    Propositional unsat core size     : 0
% 3.60/3.84  #    Propositional preprocessing time  : 0.000
% 3.60/3.84  #    Propositional encoding time       : 0.000
% 3.60/3.84  #    Propositional solver time         : 0.000
% 3.60/3.84  #    Success case prop preproc time    : 0.000
% 3.60/3.84  #    Success case prop encoding time   : 0.000
% 3.60/3.84  #    Success case prop solver time     : 0.000
% 3.60/3.84  # Current number of processed clauses  : 1263
% 3.60/3.84  #    Positive orientable unit clauses  : 226
% 3.60/3.84  #    Positive unorientable unit clauses: 0
% 3.60/3.84  #    Negative unit clauses             : 6
% 3.60/3.84  #    Non-unit-clauses                  : 1031
% 3.60/3.84  # Current number of unprocessed clauses: 437826
% 3.60/3.84  # ...number of literals in the above   : 2145911
% 3.60/3.84  # Current number of archived formulas  : 0
% 3.60/3.84  # Current number of archived clauses   : 244
% 3.60/3.84  # Clause-clause subsumption calls (NU) : 461727
% 3.60/3.84  # Rec. Clause-clause subsumption calls : 231392
% 3.60/3.84  # Non-unit clause-clause subsumptions  : 8430
% 3.60/3.84  # Unit Clause-clause subsumption calls : 15702
% 3.60/3.84  # Rewrite failures with RHS unbound    : 0
% 3.60/3.84  # BW rewrite match attempts            : 590
% 3.60/3.84  # BW rewrite match successes           : 26
% 3.60/3.84  # Condensation attempts                : 0
% 3.60/3.84  # Condensation successes               : 0
% 3.60/3.84  # Termbank termtop insertions          : 11656502
% 3.60/3.86  
% 3.60/3.86  # -------------------------------------------------
% 3.60/3.86  # User time                : 3.294 s
% 3.60/3.86  # System time              : 0.214 s
% 3.60/3.86  # Total time               : 3.508 s
% 3.60/3.86  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
