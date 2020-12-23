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
% DateTime   : Thu Dec  3 10:46:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of clauses        :   35 (  45 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  163 ( 286 expanded)
%              Number of equality atoms :   44 (  90 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t50_subset_1,conjecture,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ( ~ r2_hidden(X3,X2)
               => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(c_0_12,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X21)
        | X22 = k4_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X21)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_13,plain,(
    ! [X26,X27] : k4_xboole_0(X26,X27) = k5_xboole_0(X26,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X33,X34] : k3_xboole_0(X33,X34) = k5_xboole_0(k5_xboole_0(X33,X34),k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_15,plain,(
    ! [X28] : k3_xboole_0(X28,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X30,X31,X32] : k5_xboole_0(k5_xboole_0(X30,X31),X32) = k5_xboole_0(X30,k5_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X29] : k5_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_22,plain,
    ( X3 != k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X4,X2),k2_xboole_0(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k3_subset_1(X37,X38) = k4_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | X24 != X25 )
      & ( r1_tarski(X25,X24)
        | X24 != X25 )
      & ( ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X25,X24)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_25]),c_0_25])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X1))
           => ! [X3] :
                ( m1_subset_1(X3,X1)
               => ( ~ r2_hidden(X3,X2)
                 => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_subset_1])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_17]),c_0_18])).

cnf(c_0_38,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_17]),c_0_18])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_42,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X36,X35)
        | r2_hidden(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ r2_hidden(X36,X35)
        | m1_subset_1(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X36,X35)
        | v1_xboole_0(X36)
        | ~ v1_xboole_0(X35) )
      & ( ~ v1_xboole_0(X36)
        | m1_subset_1(X36,X35)
        | ~ v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_43,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk6_0,esk4_0)
    & ~ r2_hidden(esk6_0,esk5_0)
    & ~ r2_hidden(esk6_0,k3_subset_1(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_23])])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_23])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k3_subset_1(X2,X3))
    | r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k3_subset_1(esk4_0,esk5_0))
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k3_subset_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.46  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.028 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.46  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.46  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.46  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.46  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.46  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.46  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.46  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.46  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.46  fof(t50_subset_1, conjecture, ![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 0.19/0.46  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.46  fof(c_0_12, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X18,X15)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16)))&(~r2_hidden(X19,X15)|r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k4_xboole_0(X15,X16)))&((~r2_hidden(esk3_3(X20,X21,X22),X22)|(~r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X21))|X22=k4_xboole_0(X20,X21))&((r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))&(~r2_hidden(esk3_3(X20,X21,X22),X21)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.46  fof(c_0_13, plain, ![X26, X27]:k4_xboole_0(X26,X27)=k5_xboole_0(X26,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.46  fof(c_0_14, plain, ![X33, X34]:k3_xboole_0(X33,X34)=k5_xboole_0(k5_xboole_0(X33,X34),k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.46  fof(c_0_15, plain, ![X28]:k3_xboole_0(X28,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.46  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.46  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  fof(c_0_19, plain, ![X30, X31, X32]:k5_xboole_0(k5_xboole_0(X30,X31),X32)=k5_xboole_0(X30,k5_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.46  cnf(c_0_20, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  fof(c_0_21, plain, ![X29]:k5_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.46  cnf(c_0_22, plain, (X3!=k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X4,X2),k2_xboole_0(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.19/0.46  cnf(c_0_23, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_24, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_18])).
% 0.19/0.46  cnf(c_0_25, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.46  fof(c_0_26, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k3_subset_1(X37,X38)=k4_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.46  cnf(c_0_27, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])])).
% 0.19/0.46  cnf(c_0_28, plain, (k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.46  fof(c_0_29, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.46  cnf(c_0_30, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_31, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.46  fof(c_0_32, plain, ![X24, X25]:(((r1_tarski(X24,X25)|X24!=X25)&(r1_tarski(X25,X24)|X24!=X25))&(~r1_tarski(X24,X25)|~r1_tarski(X25,X24)|X24=X25)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.46  cnf(c_0_33, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_25]), c_0_25])])).
% 0.19/0.46  cnf(c_0_34, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.46  fof(c_0_35, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.46  fof(c_0_36, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t50_subset_1])).
% 0.19/0.46  cnf(c_0_37, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_17]), c_0_18])).
% 0.19/0.46  cnf(c_0_38, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_17]), c_0_18])).
% 0.19/0.46  cnf(c_0_39, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.46  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.46  cnf(c_0_41, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.46  fof(c_0_42, plain, ![X35, X36]:(((~m1_subset_1(X36,X35)|r2_hidden(X36,X35)|v1_xboole_0(X35))&(~r2_hidden(X36,X35)|m1_subset_1(X36,X35)|v1_xboole_0(X35)))&((~m1_subset_1(X36,X35)|v1_xboole_0(X36)|~v1_xboole_0(X35))&(~v1_xboole_0(X36)|m1_subset_1(X36,X35)|~v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.46  fof(c_0_43, negated_conjecture, (esk4_0!=k1_xboole_0&(m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk6_0,esk4_0)&(~r2_hidden(esk6_0,esk5_0)&~r2_hidden(esk6_0,k3_subset_1(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).
% 0.19/0.46  cnf(c_0_44, plain, (r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_23])])).
% 0.19/0.46  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_38, c_0_23])).
% 0.19/0.46  cnf(c_0_46, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.46  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 0.19/0.46  cnf(c_0_48, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.46  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.46  cnf(c_0_50, plain, (r2_hidden(X1,k3_subset_1(X2,X3))|r2_hidden(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.46  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.46  cnf(c_0_52, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.46  cnf(c_0_53, negated_conjecture, (r2_hidden(esk6_0,esk4_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.46  cnf(c_0_54, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.46  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,k3_subset_1(esk4_0,esk5_0))|r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.46  cnf(c_0_56, negated_conjecture, (r2_hidden(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.19/0.46  cnf(c_0_57, negated_conjecture, (~r2_hidden(esk6_0,k3_subset_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.46  cnf(c_0_58, negated_conjecture, (~r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.46  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 60
% 0.19/0.46  # Proof object clause steps            : 35
% 0.19/0.46  # Proof object formula steps           : 25
% 0.19/0.46  # Proof object conjectures             : 12
% 0.19/0.46  # Proof object clause conjectures      : 9
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 17
% 0.19/0.46  # Proof object initial formulas used   : 12
% 0.19/0.46  # Proof object generating inferences   : 10
% 0.19/0.46  # Proof object simplifying inferences  : 19
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 12
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 29
% 0.19/0.46  # Removed in clause preprocessing      : 2
% 0.19/0.46  # Initial clauses in saturation        : 27
% 0.19/0.46  # Processed clauses                    : 619
% 0.19/0.46  # ...of these trivial                  : 5
% 0.19/0.46  # ...subsumed                          : 392
% 0.19/0.46  # ...remaining for further processing  : 222
% 0.19/0.46  # Other redundant clauses eliminated   : 5
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 14
% 0.19/0.46  # Backward-rewritten                   : 28
% 0.19/0.46  # Generated clauses                    : 3420
% 0.19/0.46  # ...of the previous two non-trivial   : 3111
% 0.19/0.46  # Contextual simplify-reflections      : 5
% 0.19/0.46  # Paramodulations                      : 3411
% 0.19/0.46  # Factorizations                       : 4
% 0.19/0.46  # Equation resolutions                 : 5
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 149
% 0.19/0.46  #    Positive orientable unit clauses  : 18
% 0.19/0.46  #    Positive unorientable unit clauses: 1
% 0.19/0.46  #    Negative unit clauses             : 5
% 0.19/0.46  #    Non-unit-clauses                  : 125
% 0.19/0.46  # Current number of unprocessed clauses: 2511
% 0.19/0.46  # ...number of literals in the above   : 9386
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 70
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 1870
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 1287
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 242
% 0.19/0.46  # Unit Clause-clause subsumption calls : 66
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 51
% 0.19/0.46  # BW rewrite match successes           : 29
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 93491
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.110 s
% 0.19/0.46  # System time              : 0.008 s
% 0.19/0.46  # Total time               : 0.119 s
% 0.19/0.46  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
