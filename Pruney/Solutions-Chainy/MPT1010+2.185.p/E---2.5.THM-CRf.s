%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:37 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 107 expanded)
%              Number of clauses        :   29 (  42 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 ( 286 expanded)
%              Number of equality atoms :  102 ( 156 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t142_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(c_0_12,plain,(
    ! [X45,X46] :
      ( ( ~ r2_hidden(X45,k2_relat_1(X46))
        | k10_relat_1(X46,k1_tarski(X45)) != k1_xboole_0
        | ~ v1_relat_1(X46) )
      & ( k10_relat_1(X46,k1_tarski(X45)) = k1_xboole_0
        | r2_hidden(X45,k2_relat_1(X46))
        | ~ v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).

fof(c_0_13,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,plain,(
    ! [X43] :
      ( ~ v1_relat_1(X43)
      | k10_relat_1(X43,k2_relat_1(X43)) = k1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_18,plain,(
    ! [X44] :
      ( k1_relat_1(k6_relat_1(X44)) = X44
      & k2_relat_1(k6_relat_1(X44)) = X44 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_19,plain,(
    ! [X42] : v1_relat_1(k6_relat_1(X42)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X33,X32)
        | X33 = X27
        | X33 = X28
        | X33 = X29
        | X33 = X30
        | X33 = X31
        | X32 != k3_enumset1(X27,X28,X29,X30,X31) )
      & ( X34 != X27
        | r2_hidden(X34,X32)
        | X32 != k3_enumset1(X27,X28,X29,X30,X31) )
      & ( X34 != X28
        | r2_hidden(X34,X32)
        | X32 != k3_enumset1(X27,X28,X29,X30,X31) )
      & ( X34 != X29
        | r2_hidden(X34,X32)
        | X32 != k3_enumset1(X27,X28,X29,X30,X31) )
      & ( X34 != X30
        | r2_hidden(X34,X32)
        | X32 != k3_enumset1(X27,X28,X29,X30,X31) )
      & ( X34 != X31
        | r2_hidden(X34,X32)
        | X32 != k3_enumset1(X27,X28,X29,X30,X31) )
      & ( esk2_6(X35,X36,X37,X38,X39,X40) != X35
        | ~ r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)
        | X40 = k3_enumset1(X35,X36,X37,X38,X39) )
      & ( esk2_6(X35,X36,X37,X38,X39,X40) != X36
        | ~ r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)
        | X40 = k3_enumset1(X35,X36,X37,X38,X39) )
      & ( esk2_6(X35,X36,X37,X38,X39,X40) != X37
        | ~ r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)
        | X40 = k3_enumset1(X35,X36,X37,X38,X39) )
      & ( esk2_6(X35,X36,X37,X38,X39,X40) != X38
        | ~ r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)
        | X40 = k3_enumset1(X35,X36,X37,X38,X39) )
      & ( esk2_6(X35,X36,X37,X38,X39,X40) != X39
        | ~ r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)
        | X40 = k3_enumset1(X35,X36,X37,X38,X39) )
      & ( r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)
        | esk2_6(X35,X36,X37,X38,X39,X40) = X35
        | esk2_6(X35,X36,X37,X38,X39,X40) = X36
        | esk2_6(X35,X36,X37,X38,X39,X40) = X37
        | esk2_6(X35,X36,X37,X38,X39,X40) = X38
        | esk2_6(X35,X36,X37,X38,X39,X40) = X39
        | X40 = k3_enumset1(X35,X36,X37,X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

fof(c_0_31,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X8
        | X11 = X9
        | X10 != k2_tarski(X8,X9) )
      & ( X12 != X8
        | r2_hidden(X12,X10)
        | X10 != k2_tarski(X8,X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k2_tarski(X8,X9) )
      & ( esk1_3(X13,X14,X15) != X13
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_tarski(X13,X14) )
      & ( esk1_3(X13,X14,X15) != X14
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_tarski(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X15)
        | esk1_3(X13,X14,X15) = X13
        | esk1_3(X13,X14,X15) = X14
        | X15 = k2_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_32,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))
    & r2_hidden(esk5_0,esk3_0)
    & k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_33,plain,
    ( k10_relat_1(X2,k3_enumset1(X1,X1,X1,X1,X1)) != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_34,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X47,X48,X49,X50] :
      ( ~ v1_funct_1(X50)
      | ~ v1_funct_2(X50,X47,X48)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | ~ r2_hidden(X49,X47)
      | X48 = k1_xboole_0
      | r2_hidden(k1_funct_1(X50,X49),X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) != k1_xboole_0
    | ~ r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_29]),c_0_27])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_42,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_43,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_48,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = esk4_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t142_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.37  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.19/0.37  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.37  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.19/0.37  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.19/0.37  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 0.19/0.37  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.38  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.19/0.38  fof(c_0_12, plain, ![X45, X46]:((~r2_hidden(X45,k2_relat_1(X46))|k10_relat_1(X46,k1_tarski(X45))!=k1_xboole_0|~v1_relat_1(X46))&(k10_relat_1(X46,k1_tarski(X45))=k1_xboole_0|r2_hidden(X45,k2_relat_1(X46))|~v1_relat_1(X46))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).
% 0.19/0.38  fof(c_0_13, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  fof(c_0_14, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_15, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_16, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.38  fof(c_0_17, plain, ![X43]:(~v1_relat_1(X43)|k10_relat_1(X43,k2_relat_1(X43))=k1_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.19/0.38  fof(c_0_18, plain, ![X44]:(k1_relat_1(k6_relat_1(X44))=X44&k2_relat_1(k6_relat_1(X44))=X44), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.38  fof(c_0_19, plain, ![X42]:v1_relat_1(k6_relat_1(X42)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.19/0.38  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.19/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,k2_relat_1(X2))|k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_26, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_27, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_28, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_29, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_30, plain, ![X27, X28, X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X33,X32)|(X33=X27|X33=X28|X33=X29|X33=X30|X33=X31)|X32!=k3_enumset1(X27,X28,X29,X30,X31))&(((((X34!=X27|r2_hidden(X34,X32)|X32!=k3_enumset1(X27,X28,X29,X30,X31))&(X34!=X28|r2_hidden(X34,X32)|X32!=k3_enumset1(X27,X28,X29,X30,X31)))&(X34!=X29|r2_hidden(X34,X32)|X32!=k3_enumset1(X27,X28,X29,X30,X31)))&(X34!=X30|r2_hidden(X34,X32)|X32!=k3_enumset1(X27,X28,X29,X30,X31)))&(X34!=X31|r2_hidden(X34,X32)|X32!=k3_enumset1(X27,X28,X29,X30,X31))))&((((((esk2_6(X35,X36,X37,X38,X39,X40)!=X35|~r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)|X40=k3_enumset1(X35,X36,X37,X38,X39))&(esk2_6(X35,X36,X37,X38,X39,X40)!=X36|~r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)|X40=k3_enumset1(X35,X36,X37,X38,X39)))&(esk2_6(X35,X36,X37,X38,X39,X40)!=X37|~r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)|X40=k3_enumset1(X35,X36,X37,X38,X39)))&(esk2_6(X35,X36,X37,X38,X39,X40)!=X38|~r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)|X40=k3_enumset1(X35,X36,X37,X38,X39)))&(esk2_6(X35,X36,X37,X38,X39,X40)!=X39|~r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)|X40=k3_enumset1(X35,X36,X37,X38,X39)))&(r2_hidden(esk2_6(X35,X36,X37,X38,X39,X40),X40)|(esk2_6(X35,X36,X37,X38,X39,X40)=X35|esk2_6(X35,X36,X37,X38,X39,X40)=X36|esk2_6(X35,X36,X37,X38,X39,X40)=X37|esk2_6(X35,X36,X37,X38,X39,X40)=X38|esk2_6(X35,X36,X37,X38,X39,X40)=X39)|X40=k3_enumset1(X35,X36,X37,X38,X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.19/0.38  fof(c_0_31, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X11,X10)|(X11=X8|X11=X9)|X10!=k2_tarski(X8,X9))&((X12!=X8|r2_hidden(X12,X10)|X10!=k2_tarski(X8,X9))&(X12!=X9|r2_hidden(X12,X10)|X10!=k2_tarski(X8,X9))))&(((esk1_3(X13,X14,X15)!=X13|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_tarski(X13,X14))&(esk1_3(X13,X14,X15)!=X14|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_tarski(X13,X14)))&(r2_hidden(esk1_3(X13,X14,X15),X15)|(esk1_3(X13,X14,X15)=X13|esk1_3(X13,X14,X15)=X14)|X15=k2_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.38  fof(c_0_32, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))&(r2_hidden(esk5_0,esk3_0)&k1_funct_1(esk6_0,esk5_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.38  cnf(c_0_33, plain, (k10_relat_1(X2,k3_enumset1(X1,X1,X1,X1,X1))!=k1_xboole_0|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.19/0.38  cnf(c_0_34, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.19/0.38  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X7,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_36, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  fof(c_0_37, plain, ![X47, X48, X49, X50]:(~v1_funct_1(X50)|~v1_funct_2(X50,X47,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|(~r2_hidden(X49,X47)|(X48=k1_xboole_0|r2_hidden(k1_funct_1(X50,X49),X48)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X1,X1,X1)!=k1_xboole_0|~r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_29]), c_0_27])])).
% 0.19/0.38  cnf(c_0_41, plain, (r2_hidden(X1,k3_enumset1(X2,X3,X4,X5,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 0.19/0.38  cnf(c_0_42, plain, (X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_23]), c_0_24]), c_0_25])).
% 0.19/0.38  cnf(c_0_43, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_47, plain, (k3_enumset1(X1,X1,X1,X1,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.19/0.38  cnf(c_0_48, plain, (X1=X2|X1=X3|~r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (k1_funct_1(esk6_0,X1)=esk4_0|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 54
% 0.19/0.38  # Proof object clause steps            : 29
% 0.19/0.38  # Proof object formula steps           : 25
% 0.19/0.38  # Proof object conjectures             : 13
% 0.19/0.38  # Proof object clause conjectures      : 10
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 17
% 0.19/0.38  # Proof object initial formulas used   : 12
% 0.19/0.38  # Proof object generating inferences   : 5
% 0.19/0.38  # Proof object simplifying inferences  : 32
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 12
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 34
% 0.19/0.38  # Removed in clause preprocessing      : 4
% 0.19/0.38  # Initial clauses in saturation        : 30
% 0.19/0.38  # Processed clauses                    : 55
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 8
% 0.19/0.38  # ...remaining for further processing  : 47
% 0.19/0.38  # Other redundant clauses eliminated   : 25
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 1
% 0.19/0.38  # Generated clauses                    : 110
% 0.19/0.38  # ...of the previous two non-trivial   : 89
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 92
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 25
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 38
% 0.19/0.38  #    Positive orientable unit clauses  : 13
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 23
% 0.19/0.38  # Current number of unprocessed clauses: 64
% 0.19/0.38  # ...number of literals in the above   : 359
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 5
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 40
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 39
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.19/0.38  # Unit Clause-clause subsumption calls : 10
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 15
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3470
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.033 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
