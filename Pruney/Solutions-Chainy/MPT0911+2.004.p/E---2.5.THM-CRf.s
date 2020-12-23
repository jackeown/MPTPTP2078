%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:14 EST 2020

% Result     : Theorem 23.03s
% Output     : CNFRefutation 23.03s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 564 expanded)
%              Number of clauses        :   57 ( 254 expanded)
%              Number of leaves         :   11 ( 134 expanded)
%              Depth                    :   14
%              Number of atoms          :  256 (2765 expanded)
%              Number of equality atoms :  110 (1267 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X8 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

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

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X8 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t71_mcart_1])).

fof(c_0_12,plain,(
    ! [X31,X32,X33,X34,X37,X38,X39,X40,X41,X42,X44,X45] :
      ( ( r2_hidden(esk3_4(X31,X32,X33,X34),X31)
        | ~ r2_hidden(X34,X33)
        | X33 != k2_zfmisc_1(X31,X32) )
      & ( r2_hidden(esk4_4(X31,X32,X33,X34),X32)
        | ~ r2_hidden(X34,X33)
        | X33 != k2_zfmisc_1(X31,X32) )
      & ( X34 = k4_tarski(esk3_4(X31,X32,X33,X34),esk4_4(X31,X32,X33,X34))
        | ~ r2_hidden(X34,X33)
        | X33 != k2_zfmisc_1(X31,X32) )
      & ( ~ r2_hidden(X38,X31)
        | ~ r2_hidden(X39,X32)
        | X37 != k4_tarski(X38,X39)
        | r2_hidden(X37,X33)
        | X33 != k2_zfmisc_1(X31,X32) )
      & ( ~ r2_hidden(esk5_3(X40,X41,X42),X42)
        | ~ r2_hidden(X44,X40)
        | ~ r2_hidden(X45,X41)
        | esk5_3(X40,X41,X42) != k4_tarski(X44,X45)
        | X42 = k2_zfmisc_1(X40,X41) )
      & ( r2_hidden(esk6_3(X40,X41,X42),X40)
        | r2_hidden(esk5_3(X40,X41,X42),X42)
        | X42 = k2_zfmisc_1(X40,X41) )
      & ( r2_hidden(esk7_3(X40,X41,X42),X41)
        | r2_hidden(esk5_3(X40,X41,X42),X42)
        | X42 = k2_zfmisc_1(X40,X41) )
      & ( esk5_3(X40,X41,X42) = k4_tarski(esk6_3(X40,X41,X42),esk7_3(X40,X41,X42))
        | r2_hidden(esk5_3(X40,X41,X42),X42)
        | X42 = k2_zfmisc_1(X40,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_13,negated_conjecture,(
    ! [X84,X85,X86] :
      ( m1_subset_1(esk13_0,k3_zfmisc_1(esk9_0,esk10_0,esk11_0))
      & ( ~ m1_subset_1(X84,esk9_0)
        | ~ m1_subset_1(X85,esk10_0)
        | ~ m1_subset_1(X86,esk11_0)
        | esk13_0 != k3_mcart_1(X84,X85,X86)
        | esk12_0 = X86 )
      & esk9_0 != k1_xboole_0
      & esk10_0 != k1_xboole_0
      & esk11_0 != k1_xboole_0
      & esk12_0 != k7_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X66,X68,X69,X70,X71] :
      ( ( r2_hidden(esk8_1(X66),X66)
        | X66 = k1_xboole_0 )
      & ( ~ r2_hidden(X68,X66)
        | esk8_1(X66) != k4_mcart_1(X68,X69,X70,X71)
        | X66 = k1_xboole_0 )
      & ( ~ r2_hidden(X69,X66)
        | esk8_1(X66) != k4_mcart_1(X68,X69,X70,X71)
        | X66 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

fof(c_0_15,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk8_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X58,X59,X60] : k3_zfmisc_1(X58,X59,X60) = k2_zfmisc_1(k2_zfmisc_1(X58,X59),X60) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk11_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk8_1(esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_26,plain,(
    ! [X51,X52] :
      ( ( ~ m1_subset_1(X52,X51)
        | r2_hidden(X52,X51)
        | v1_xboole_0(X51) )
      & ( ~ r2_hidden(X52,X51)
        | m1_subset_1(X52,X51)
        | v1_xboole_0(X51) )
      & ( ~ m1_subset_1(X52,X51)
        | v1_xboole_0(X52)
        | ~ v1_xboole_0(X51) )
      & ( ~ v1_xboole_0(X52)
        | m1_subset_1(X52,X51)
        | ~ v1_xboole_0(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk13_0,k3_zfmisc_1(esk9_0,esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk8_1(esk11_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_1(esk9_0),X1),k2_zfmisc_1(esk9_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk8_1(esk10_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk13_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_1(esk11_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_1(esk9_0),esk8_1(esk10_0)),k2_zfmisc_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk13_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_1(esk11_0)),k2_zfmisc_1(X2,esk11_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_1(k2_zfmisc_1(esk9_0,esk10_0)),k2_zfmisc_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_36])).

fof(c_0_40,plain,(
    ! [X75,X76,X77,X78] :
      ( ( k5_mcart_1(X75,X76,X77,X78) = k1_mcart_1(k1_mcart_1(X78))
        | ~ m1_subset_1(X78,k3_zfmisc_1(X75,X76,X77))
        | X75 = k1_xboole_0
        | X76 = k1_xboole_0
        | X77 = k1_xboole_0 )
      & ( k6_mcart_1(X75,X76,X77,X78) = k2_mcart_1(k1_mcart_1(X78))
        | ~ m1_subset_1(X78,k3_zfmisc_1(X75,X76,X77))
        | X75 = k1_xboole_0
        | X76 = k1_xboole_0
        | X77 = k1_xboole_0 )
      & ( k7_mcart_1(X75,X76,X77,X78) = k2_mcart_1(X78)
        | ~ m1_subset_1(X78,k3_zfmisc_1(X75,X76,X77))
        | X75 = k1_xboole_0
        | X76 = k1_xboole_0
        | X77 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_41,plain,(
    ! [X61,X62,X63] :
      ( ( r2_hidden(k1_mcart_1(X61),X62)
        | ~ r2_hidden(X61,k2_zfmisc_1(X62,X63)) )
      & ( r2_hidden(k2_mcart_1(X61),X63)
        | ~ r2_hidden(X61,k2_zfmisc_1(X62,X63)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk13_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_1(k2_zfmisc_1(esk9_0,esk10_0)),esk1_1(esk11_0)),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_46,plain,(
    ! [X64,X65] :
      ( ~ v1_relat_1(X65)
      | ~ r2_hidden(X64,X65)
      | X64 = k4_tarski(k1_mcart_1(X64),k2_mcart_1(X64)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_47,plain,(
    ! [X53,X54] : v1_relat_1(k2_zfmisc_1(X53,X54)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_48,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk13_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_28])).

cnf(c_0_51,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_28])).

fof(c_0_52,plain,(
    ! [X55,X56,X57] : k3_mcart_1(X55,X56,X57) = k4_tarski(k4_tarski(X55,X56),X57) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_53,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_56,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk13_0),k2_zfmisc_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk13_0)) = k6_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_34]),c_0_22]),c_0_25]),c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk13_0)) = k5_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_34]),c_0_22]),c_0_25]),c_0_17])).

cnf(c_0_60,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( esk12_0 = X3
    | ~ m1_subset_1(X1,esk9_0)
    | ~ m1_subset_1(X2,esk10_0)
    | ~ m1_subset_1(X3,esk11_0)
    | esk13_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_62,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_55,c_0_20])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k6_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0),esk10_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k5_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0),esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_57]),c_0_59])).

cnf(c_0_67,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_28])).

cnf(c_0_68,negated_conjecture,
    ( esk12_0 = X3
    | esk13_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk11_0)
    | ~ m1_subset_1(X2,esk10_0)
    | ~ m1_subset_1(X1,esk9_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0),k6_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0)) = k1_mcart_1(esk13_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_57]),c_0_59]),c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k5_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk13_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_49])).

cnf(c_0_73,negated_conjecture,
    ( esk12_0 != k7_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_74,negated_conjecture,
    ( k7_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0) = k2_mcart_1(esk13_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_34]),c_0_22]),c_0_25]),c_0_17])).

cnf(c_0_75,negated_conjecture,
    ( esk12_0 = X1
    | k4_tarski(k1_mcart_1(esk13_0),X1) != esk13_0
    | ~ m1_subset_1(X1,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71])])).

cnf(c_0_76,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk13_0),k2_mcart_1(esk13_0)) = esk13_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_49])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk13_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k2_mcart_1(esk13_0) != esk12_0 ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])]),c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 23.03/23.23  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 23.03/23.23  # and selection function SelectNegativeLiterals.
% 23.03/23.23  #
% 23.03/23.23  # Preprocessing time       : 0.029 s
% 23.03/23.23  # Presaturation interreduction done
% 23.03/23.23  
% 23.03/23.23  # Proof found!
% 23.03/23.23  # SZS status Theorem
% 23.03/23.23  # SZS output start CNFRefutation
% 23.03/23.23  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 23.03/23.23  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 23.03/23.23  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 23.03/23.23  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 23.03/23.23  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 23.03/23.23  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 23.03/23.23  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 23.03/23.23  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 23.03/23.23  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 23.03/23.23  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 23.03/23.23  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 23.03/23.23  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 23.03/23.23  fof(c_0_12, plain, ![X31, X32, X33, X34, X37, X38, X39, X40, X41, X42, X44, X45]:(((((r2_hidden(esk3_4(X31,X32,X33,X34),X31)|~r2_hidden(X34,X33)|X33!=k2_zfmisc_1(X31,X32))&(r2_hidden(esk4_4(X31,X32,X33,X34),X32)|~r2_hidden(X34,X33)|X33!=k2_zfmisc_1(X31,X32)))&(X34=k4_tarski(esk3_4(X31,X32,X33,X34),esk4_4(X31,X32,X33,X34))|~r2_hidden(X34,X33)|X33!=k2_zfmisc_1(X31,X32)))&(~r2_hidden(X38,X31)|~r2_hidden(X39,X32)|X37!=k4_tarski(X38,X39)|r2_hidden(X37,X33)|X33!=k2_zfmisc_1(X31,X32)))&((~r2_hidden(esk5_3(X40,X41,X42),X42)|(~r2_hidden(X44,X40)|~r2_hidden(X45,X41)|esk5_3(X40,X41,X42)!=k4_tarski(X44,X45))|X42=k2_zfmisc_1(X40,X41))&(((r2_hidden(esk6_3(X40,X41,X42),X40)|r2_hidden(esk5_3(X40,X41,X42),X42)|X42=k2_zfmisc_1(X40,X41))&(r2_hidden(esk7_3(X40,X41,X42),X41)|r2_hidden(esk5_3(X40,X41,X42),X42)|X42=k2_zfmisc_1(X40,X41)))&(esk5_3(X40,X41,X42)=k4_tarski(esk6_3(X40,X41,X42),esk7_3(X40,X41,X42))|r2_hidden(esk5_3(X40,X41,X42),X42)|X42=k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 23.03/23.23  fof(c_0_13, negated_conjecture, ![X84, X85, X86]:(m1_subset_1(esk13_0,k3_zfmisc_1(esk9_0,esk10_0,esk11_0))&((~m1_subset_1(X84,esk9_0)|(~m1_subset_1(X85,esk10_0)|(~m1_subset_1(X86,esk11_0)|(esk13_0!=k3_mcart_1(X84,X85,X86)|esk12_0=X86))))&(((esk9_0!=k1_xboole_0&esk10_0!=k1_xboole_0)&esk11_0!=k1_xboole_0)&esk12_0!=k7_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 23.03/23.23  fof(c_0_14, plain, ![X66, X68, X69, X70, X71]:((r2_hidden(esk8_1(X66),X66)|X66=k1_xboole_0)&((~r2_hidden(X68,X66)|esk8_1(X66)!=k4_mcart_1(X68,X69,X70,X71)|X66=k1_xboole_0)&(~r2_hidden(X69,X66)|esk8_1(X66)!=k4_mcart_1(X68,X69,X70,X71)|X66=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 23.03/23.23  fof(c_0_15, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 23.03/23.23  cnf(c_0_16, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 23.03/23.23  cnf(c_0_17, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.03/23.23  cnf(c_0_18, plain, (r2_hidden(esk8_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 23.03/23.23  fof(c_0_19, plain, ![X58, X59, X60]:k3_zfmisc_1(X58,X59,X60)=k2_zfmisc_1(k2_zfmisc_1(X58,X59),X60), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 23.03/23.23  cnf(c_0_20, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 23.03/23.23  cnf(c_0_21, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 23.03/23.23  cnf(c_0_22, negated_conjecture, (esk11_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.03/23.23  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).
% 23.03/23.23  cnf(c_0_24, negated_conjecture, (r2_hidden(esk8_1(esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 23.03/23.23  cnf(c_0_25, negated_conjecture, (esk10_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.03/23.23  fof(c_0_26, plain, ![X51, X52]:(((~m1_subset_1(X52,X51)|r2_hidden(X52,X51)|v1_xboole_0(X51))&(~r2_hidden(X52,X51)|m1_subset_1(X52,X51)|v1_xboole_0(X51)))&((~m1_subset_1(X52,X51)|v1_xboole_0(X52)|~v1_xboole_0(X51))&(~v1_xboole_0(X52)|m1_subset_1(X52,X51)|~v1_xboole_0(X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 23.03/23.23  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk13_0,k3_zfmisc_1(esk9_0,esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.03/23.23  cnf(c_0_28, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 23.03/23.23  cnf(c_0_29, plain, (r2_hidden(esk1_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 23.03/23.23  cnf(c_0_30, negated_conjecture, (r2_hidden(esk8_1(esk11_0),esk11_0)), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 23.03/23.23  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(esk8_1(esk9_0),X1),k2_zfmisc_1(esk9_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 23.03/23.23  cnf(c_0_32, negated_conjecture, (r2_hidden(esk8_1(esk10_0),esk10_0)), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 23.03/23.23  cnf(c_0_33, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 23.03/23.23  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk13_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 23.03/23.23  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_1(esk11_0),esk11_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 23.03/23.23  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(esk8_1(esk9_0),esk8_1(esk10_0)),k2_zfmisc_1(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 23.03/23.23  cnf(c_0_37, negated_conjecture, (r2_hidden(esk13_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 23.03/23.23  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(X1,esk1_1(esk11_0)),k2_zfmisc_1(X2,esk11_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_35])).
% 23.03/23.23  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_1(k2_zfmisc_1(esk9_0,esk10_0)),k2_zfmisc_1(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_29, c_0_36])).
% 23.03/23.23  fof(c_0_40, plain, ![X75, X76, X77, X78]:(((k5_mcart_1(X75,X76,X77,X78)=k1_mcart_1(k1_mcart_1(X78))|~m1_subset_1(X78,k3_zfmisc_1(X75,X76,X77))|(X75=k1_xboole_0|X76=k1_xboole_0|X77=k1_xboole_0))&(k6_mcart_1(X75,X76,X77,X78)=k2_mcart_1(k1_mcart_1(X78))|~m1_subset_1(X78,k3_zfmisc_1(X75,X76,X77))|(X75=k1_xboole_0|X76=k1_xboole_0|X77=k1_xboole_0)))&(k7_mcart_1(X75,X76,X77,X78)=k2_mcart_1(X78)|~m1_subset_1(X78,k3_zfmisc_1(X75,X76,X77))|(X75=k1_xboole_0|X76=k1_xboole_0|X77=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 23.03/23.23  fof(c_0_41, plain, ![X61, X62, X63]:((r2_hidden(k1_mcart_1(X61),X62)|~r2_hidden(X61,k2_zfmisc_1(X62,X63)))&(r2_hidden(k2_mcart_1(X61),X63)|~r2_hidden(X61,k2_zfmisc_1(X62,X63)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 23.03/23.23  cnf(c_0_42, negated_conjecture, (r2_hidden(esk13_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))), inference(spm,[status(thm)],[c_0_20, c_0_37])).
% 23.03/23.23  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk1_1(k2_zfmisc_1(esk9_0,esk10_0)),esk1_1(esk11_0)),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 23.03/23.23  cnf(c_0_44, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 23.03/23.23  cnf(c_0_45, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 23.03/23.23  fof(c_0_46, plain, ![X64, X65]:(~v1_relat_1(X65)|(~r2_hidden(X64,X65)|X64=k4_tarski(k1_mcart_1(X64),k2_mcart_1(X64)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 23.03/23.23  fof(c_0_47, plain, ![X53, X54]:v1_relat_1(k2_zfmisc_1(X53,X54)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 23.03/23.23  cnf(c_0_48, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 23.03/23.23  cnf(c_0_49, negated_conjecture, (r2_hidden(esk13_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 23.03/23.23  cnf(c_0_50, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_44, c_0_28])).
% 23.03/23.23  cnf(c_0_51, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_45, c_0_28])).
% 23.03/23.23  fof(c_0_52, plain, ![X55, X56, X57]:k3_mcart_1(X55,X56,X57)=k4_tarski(k4_tarski(X55,X56),X57), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 23.03/23.23  cnf(c_0_53, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 23.03/23.23  cnf(c_0_54, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 23.03/23.23  cnf(c_0_55, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 23.03/23.23  cnf(c_0_56, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 23.03/23.23  cnf(c_0_57, negated_conjecture, (r2_hidden(k1_mcart_1(esk13_0),k2_zfmisc_1(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 23.03/23.23  cnf(c_0_58, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk13_0))=k6_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_34]), c_0_22]), c_0_25]), c_0_17])).
% 23.03/23.23  cnf(c_0_59, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk13_0))=k5_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_34]), c_0_22]), c_0_25]), c_0_17])).
% 23.03/23.23  cnf(c_0_60, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 23.03/23.23  cnf(c_0_61, negated_conjecture, (esk12_0=X3|~m1_subset_1(X1,esk9_0)|~m1_subset_1(X2,esk10_0)|~m1_subset_1(X3,esk11_0)|esk13_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.03/23.23  cnf(c_0_62, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 23.03/23.23  cnf(c_0_63, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 23.03/23.23  cnf(c_0_64, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_55, c_0_20])).
% 23.03/23.23  cnf(c_0_65, negated_conjecture, (r2_hidden(k6_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0),esk10_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 23.03/23.23  cnf(c_0_66, negated_conjecture, (r2_hidden(k5_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0),esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_57]), c_0_59])).
% 23.03/23.23  cnf(c_0_67, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_60, c_0_28])).
% 23.03/23.23  cnf(c_0_68, negated_conjecture, (esk12_0=X3|esk13_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk11_0)|~m1_subset_1(X2,esk10_0)|~m1_subset_1(X1,esk9_0)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 23.03/23.23  cnf(c_0_69, negated_conjecture, (k4_tarski(k5_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0),k6_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0))=k1_mcart_1(esk13_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_57]), c_0_59]), c_0_58])).
% 23.03/23.23  cnf(c_0_70, negated_conjecture, (m1_subset_1(k6_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0),esk10_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 23.03/23.23  cnf(c_0_71, negated_conjecture, (m1_subset_1(k5_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0),esk9_0)), inference(spm,[status(thm)],[c_0_64, c_0_66])).
% 23.03/23.23  cnf(c_0_72, negated_conjecture, (r2_hidden(k2_mcart_1(esk13_0),esk11_0)), inference(spm,[status(thm)],[c_0_56, c_0_49])).
% 23.03/23.23  cnf(c_0_73, negated_conjecture, (esk12_0!=k7_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.03/23.23  cnf(c_0_74, negated_conjecture, (k7_mcart_1(esk9_0,esk10_0,esk11_0,esk13_0)=k2_mcart_1(esk13_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_34]), c_0_22]), c_0_25]), c_0_17])).
% 23.03/23.23  cnf(c_0_75, negated_conjecture, (esk12_0=X1|k4_tarski(k1_mcart_1(esk13_0),X1)!=esk13_0|~m1_subset_1(X1,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71])])).
% 23.03/23.23  cnf(c_0_76, negated_conjecture, (k4_tarski(k1_mcart_1(esk13_0),k2_mcart_1(esk13_0))=esk13_0), inference(spm,[status(thm)],[c_0_63, c_0_49])).
% 23.03/23.23  cnf(c_0_77, negated_conjecture, (m1_subset_1(k2_mcart_1(esk13_0),esk11_0)), inference(spm,[status(thm)],[c_0_64, c_0_72])).
% 23.03/23.23  cnf(c_0_78, negated_conjecture, (k2_mcart_1(esk13_0)!=esk12_0), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 23.03/23.23  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])]), c_0_78]), ['proof']).
% 23.03/23.23  # SZS output end CNFRefutation
% 23.03/23.23  # Proof object total steps             : 80
% 23.03/23.23  # Proof object clause steps            : 57
% 23.03/23.23  # Proof object formula steps           : 23
% 23.03/23.23  # Proof object conjectures             : 38
% 23.03/23.23  # Proof object clause conjectures      : 35
% 23.03/23.23  # Proof object formula conjectures     : 3
% 23.03/23.23  # Proof object initial clauses used    : 21
% 23.03/23.23  # Proof object initial formulas used   : 11
% 23.03/23.23  # Proof object generating inferences   : 28
% 23.03/23.23  # Proof object simplifying inferences  : 28
% 23.03/23.23  # Training examples: 0 positive, 0 negative
% 23.03/23.23  # Parsed axioms                        : 19
% 23.03/23.23  # Removed by relevancy pruning/SinE    : 0
% 23.03/23.23  # Initial clauses                      : 50
% 23.03/23.23  # Removed in clause preprocessing      : 4
% 23.03/23.23  # Initial clauses in saturation        : 46
% 23.03/23.23  # Processed clauses                    : 11624
% 23.03/23.23  # ...of these trivial                  : 786
% 23.03/23.23  # ...subsumed                          : 5137
% 23.03/23.23  # ...remaining for further processing  : 5701
% 23.03/23.23  # Other redundant clauses eliminated   : 6319
% 23.03/23.23  # Clauses deleted for lack of memory   : 102534
% 23.03/23.23  # Backward-subsumed                    : 172
% 23.03/23.23  # Backward-rewritten                   : 349
% 23.03/23.23  # Generated clauses                    : 3435717
% 23.03/23.23  # ...of the previous two non-trivial   : 2924326
% 23.03/23.23  # Contextual simplify-reflections      : 11
% 23.03/23.23  # Paramodulations                      : 3429216
% 23.03/23.23  # Factorizations                       : 185
% 23.03/23.23  # Equation resolutions                 : 6319
% 23.03/23.23  # Propositional unsat checks           : 0
% 23.03/23.23  #    Propositional check models        : 0
% 23.03/23.23  #    Propositional check unsatisfiable : 0
% 23.03/23.23  #    Propositional clauses             : 0
% 23.03/23.23  #    Propositional clauses after purity: 0
% 23.03/23.23  #    Propositional unsat core size     : 0
% 23.03/23.23  #    Propositional preprocessing time  : 0.000
% 23.03/23.23  #    Propositional encoding time       : 0.000
% 23.03/23.23  #    Propositional solver time         : 0.000
% 23.03/23.23  #    Success case prop preproc time    : 0.000
% 23.03/23.23  #    Success case prop encoding time   : 0.000
% 23.03/23.23  #    Success case prop solver time     : 0.000
% 23.03/23.23  # Current number of processed clauses  : 5124
% 23.03/23.23  #    Positive orientable unit clauses  : 2218
% 23.03/23.23  #    Positive unorientable unit clauses: 0
% 23.03/23.23  #    Negative unit clauses             : 11
% 23.03/23.23  #    Non-unit-clauses                  : 2895
% 23.03/23.23  # Current number of unprocessed clauses: 1745718
% 23.03/23.23  # ...number of literals in the above   : 4489755
% 23.03/23.23  # Current number of archived formulas  : 0
% 23.03/23.23  # Current number of archived clauses   : 571
% 23.03/23.23  # Clause-clause subsumption calls (NU) : 1596015
% 23.03/23.23  # Rec. Clause-clause subsumption calls : 1195495
% 23.03/23.23  # Non-unit clause-clause subsumptions  : 5290
% 23.03/23.23  # Unit Clause-clause subsumption calls : 413938
% 23.03/23.23  # Rewrite failures with RHS unbound    : 0
% 23.03/23.23  # BW rewrite match attempts            : 12971
% 23.03/23.23  # BW rewrite match successes           : 243
% 23.03/23.23  # Condensation attempts                : 0
% 23.03/23.23  # Condensation successes               : 0
% 23.03/23.23  # Termbank termtop insertions          : 67261270
% 23.10/23.31  
% 23.10/23.31  # -------------------------------------------------
% 23.10/23.31  # User time                : 22.019 s
% 23.10/23.31  # System time              : 0.940 s
% 23.10/23.31  # Total time               : 22.959 s
% 23.10/23.31  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
