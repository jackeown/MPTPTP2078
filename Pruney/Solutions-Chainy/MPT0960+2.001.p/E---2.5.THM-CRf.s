%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:47 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 106 expanded)
%              Number of clauses        :   21 (  46 expanded)
%              Number of leaves         :    7 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 305 expanded)
%              Number of equality atoms :   22 (  49 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_wellord2,conjecture,(
    ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t33_wellord2])).

fof(c_0_8,plain,(
    ! [X39,X40,X41,X42] :
      ( ( k3_relat_1(X40) = X39
        | X40 != k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( ~ r2_hidden(k4_tarski(X41,X42),X40)
        | r1_tarski(X41,X42)
        | ~ r2_hidden(X41,X39)
        | ~ r2_hidden(X42,X39)
        | X40 != k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( ~ r1_tarski(X41,X42)
        | r2_hidden(k4_tarski(X41,X42),X40)
        | ~ r2_hidden(X41,X39)
        | ~ r2_hidden(X42,X39)
        | X40 != k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(esk5_2(X39,X40),X39)
        | k3_relat_1(X40) != X39
        | X40 = k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(esk6_2(X39,X40),X39)
        | k3_relat_1(X40) != X39
        | X40 = k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X39,X40),esk6_2(X39,X40)),X40)
        | ~ r1_tarski(esk5_2(X39,X40),esk6_2(X39,X40))
        | k3_relat_1(X40) != X39
        | X40 = k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(k4_tarski(esk5_2(X39,X40),esk6_2(X39,X40)),X40)
        | r1_tarski(esk5_2(X39,X40),esk6_2(X39,X40))
        | k3_relat_1(X40) != X39
        | X40 = k1_wellord2(X39)
        | ~ v1_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_9,plain,(
    ! [X45] : v1_relat_1(k1_wellord2(X45)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_10,negated_conjecture,(
    ~ r1_tarski(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,k3_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(X37,k3_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_13,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X28,X29,X32,X34,X35] :
      ( ( ~ v1_relat_1(X28)
        | ~ r2_hidden(X29,X28)
        | X29 = k4_tarski(esk2_2(X28,X29),esk3_2(X28,X29)) )
      & ( r2_hidden(esk4_1(X32),X32)
        | v1_relat_1(X32) )
      & ( esk4_1(X32) != k4_tarski(X34,X35)
        | v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])])).

cnf(c_0_20,plain,
    ( X2 = k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)),k1_wellord2(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k1_wellord2(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_14])])).

cnf(c_0_23,negated_conjecture,
    ( k4_tarski(esk2_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))),esk3_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)))) = esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_25,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_hidden(X18,X20)
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)) )
      & ( r2_hidden(X19,X21)
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)) )
      & ( ~ r2_hidden(X18,X20)
        | ~ r2_hidden(X19,X21)
        | r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))),X1)
    | ~ r2_hidden(esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k1_wellord2(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_14])])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))),X1)
    | ~ r2_hidden(esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk3_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)))),k2_zfmisc_1(X2,esk7_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)),k2_zfmisc_1(esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:36:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.60  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S015I
% 0.42/0.60  # and selection function PSelectOptimalLit.
% 0.42/0.60  #
% 0.42/0.60  # Preprocessing time       : 0.028 s
% 0.42/0.60  # Presaturation interreduction done
% 0.42/0.60  
% 0.42/0.60  # Proof found!
% 0.42/0.60  # SZS status Theorem
% 0.42/0.60  # SZS output start CNFRefutation
% 0.42/0.60  fof(t33_wellord2, conjecture, ![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 0.42/0.60  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.42/0.60  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.42/0.60  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.42/0.60  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.42/0.60  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.42/0.60  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.42/0.60  fof(c_0_7, negated_conjecture, ~(![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))), inference(assume_negation,[status(cth)],[t33_wellord2])).
% 0.42/0.60  fof(c_0_8, plain, ![X39, X40, X41, X42]:(((k3_relat_1(X40)=X39|X40!=k1_wellord2(X39)|~v1_relat_1(X40))&((~r2_hidden(k4_tarski(X41,X42),X40)|r1_tarski(X41,X42)|(~r2_hidden(X41,X39)|~r2_hidden(X42,X39))|X40!=k1_wellord2(X39)|~v1_relat_1(X40))&(~r1_tarski(X41,X42)|r2_hidden(k4_tarski(X41,X42),X40)|(~r2_hidden(X41,X39)|~r2_hidden(X42,X39))|X40!=k1_wellord2(X39)|~v1_relat_1(X40))))&(((r2_hidden(esk5_2(X39,X40),X39)|k3_relat_1(X40)!=X39|X40=k1_wellord2(X39)|~v1_relat_1(X40))&(r2_hidden(esk6_2(X39,X40),X39)|k3_relat_1(X40)!=X39|X40=k1_wellord2(X39)|~v1_relat_1(X40)))&((~r2_hidden(k4_tarski(esk5_2(X39,X40),esk6_2(X39,X40)),X40)|~r1_tarski(esk5_2(X39,X40),esk6_2(X39,X40))|k3_relat_1(X40)!=X39|X40=k1_wellord2(X39)|~v1_relat_1(X40))&(r2_hidden(k4_tarski(esk5_2(X39,X40),esk6_2(X39,X40)),X40)|r1_tarski(esk5_2(X39,X40),esk6_2(X39,X40))|k3_relat_1(X40)!=X39|X40=k1_wellord2(X39)|~v1_relat_1(X40))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.42/0.60  fof(c_0_9, plain, ![X45]:v1_relat_1(k1_wellord2(X45)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.42/0.60  fof(c_0_10, negated_conjecture, ~r1_tarski(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.42/0.60  fof(c_0_11, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.42/0.60  fof(c_0_12, plain, ![X36, X37, X38]:((r2_hidden(X36,k3_relat_1(X38))|~r2_hidden(k4_tarski(X36,X37),X38)|~v1_relat_1(X38))&(r2_hidden(X37,k3_relat_1(X38))|~r2_hidden(k4_tarski(X36,X37),X38)|~v1_relat_1(X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.42/0.60  cnf(c_0_13, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.42/0.60  cnf(c_0_14, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.42/0.60  fof(c_0_15, plain, ![X28, X29, X32, X34, X35]:((~v1_relat_1(X28)|(~r2_hidden(X29,X28)|X29=k4_tarski(esk2_2(X28,X29),esk3_2(X28,X29))))&((r2_hidden(esk4_1(X32),X32)|v1_relat_1(X32))&(esk4_1(X32)!=k4_tarski(X34,X35)|v1_relat_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.42/0.60  cnf(c_0_16, negated_conjecture, (~r1_tarski(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.42/0.60  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.42/0.60  cnf(c_0_18, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.42/0.60  cnf(c_0_19, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_14])])).
% 0.42/0.60  cnf(c_0_20, plain, (X2=k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.60  cnf(c_0_21, negated_conjecture, (r2_hidden(esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)),k1_wellord2(esk7_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.42/0.60  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k1_wellord2(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_14])])).
% 0.42/0.60  cnf(c_0_23, negated_conjecture, (k4_tarski(esk2_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))),esk3_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))))=esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_14])])).
% 0.42/0.60  cnf(c_0_24, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.42/0.60  fof(c_0_25, plain, ![X18, X19, X20, X21]:(((r2_hidden(X18,X20)|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)))&(r2_hidden(X19,X21)|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21))))&(~r2_hidden(X18,X20)|~r2_hidden(X19,X21)|r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.42/0.60  cnf(c_0_26, negated_conjecture, (r2_hidden(esk3_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))),X1)|~r2_hidden(esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.42/0.60  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k1_wellord2(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_14])])).
% 0.42/0.60  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.60  cnf(c_0_29, negated_conjecture, (r2_hidden(esk3_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))),esk7_0)), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 0.42/0.60  cnf(c_0_30, negated_conjecture, (r2_hidden(esk2_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))),X1)|~r2_hidden(esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_27, c_0_23])).
% 0.42/0.60  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(X1,esk3_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)))),k2_zfmisc_1(X2,esk7_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.42/0.60  cnf(c_0_32, negated_conjecture, (r2_hidden(esk2_2(k1_wellord2(esk7_0),esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0))),esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_21])).
% 0.42/0.60  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.42/0.60  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(k1_wellord2(esk7_0),k2_zfmisc_1(esk7_0,esk7_0)),k2_zfmisc_1(esk7_0,esk7_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_23])).
% 0.42/0.60  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_16]), ['proof']).
% 0.42/0.60  # SZS output end CNFRefutation
% 0.42/0.60  # Proof object total steps             : 36
% 0.42/0.60  # Proof object clause steps            : 21
% 0.42/0.60  # Proof object formula steps           : 15
% 0.42/0.60  # Proof object conjectures             : 13
% 0.42/0.60  # Proof object clause conjectures      : 10
% 0.42/0.60  # Proof object formula conjectures     : 3
% 0.42/0.60  # Proof object initial clauses used    : 9
% 0.42/0.60  # Proof object initial formulas used   : 7
% 0.42/0.60  # Proof object generating inferences   : 11
% 0.42/0.60  # Proof object simplifying inferences  : 11
% 0.42/0.60  # Training examples: 0 positive, 0 negative
% 0.42/0.60  # Parsed axioms                        : 13
% 0.42/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.60  # Initial clauses                      : 27
% 0.42/0.60  # Removed in clause preprocessing      : 0
% 0.42/0.60  # Initial clauses in saturation        : 27
% 0.42/0.60  # Processed clauses                    : 1499
% 0.42/0.60  # ...of these trivial                  : 47
% 0.42/0.60  # ...subsumed                          : 669
% 0.42/0.60  # ...remaining for further processing  : 783
% 0.42/0.60  # Other redundant clauses eliminated   : 7
% 0.42/0.60  # Clauses deleted for lack of memory   : 0
% 0.42/0.60  # Backward-subsumed                    : 13
% 0.42/0.60  # Backward-rewritten                   : 3
% 0.42/0.60  # Generated clauses                    : 14449
% 0.42/0.60  # ...of the previous two non-trivial   : 13315
% 0.42/0.60  # Contextual simplify-reflections      : 2
% 0.42/0.60  # Paramodulations                      : 14422
% 0.42/0.60  # Factorizations                       : 20
% 0.42/0.60  # Equation resolutions                 : 7
% 0.42/0.60  # Propositional unsat checks           : 0
% 0.42/0.60  #    Propositional check models        : 0
% 0.42/0.60  #    Propositional check unsatisfiable : 0
% 0.42/0.60  #    Propositional clauses             : 0
% 0.42/0.60  #    Propositional clauses after purity: 0
% 0.42/0.60  #    Propositional unsat core size     : 0
% 0.42/0.60  #    Propositional preprocessing time  : 0.000
% 0.42/0.60  #    Propositional encoding time       : 0.000
% 0.42/0.60  #    Propositional solver time         : 0.000
% 0.42/0.60  #    Success case prop preproc time    : 0.000
% 0.42/0.60  #    Success case prop encoding time   : 0.000
% 0.42/0.60  #    Success case prop solver time     : 0.000
% 0.42/0.60  # Current number of processed clauses  : 733
% 0.42/0.60  #    Positive orientable unit clauses  : 116
% 0.42/0.60  #    Positive unorientable unit clauses: 0
% 0.42/0.60  #    Negative unit clauses             : 1
% 0.42/0.60  #    Non-unit-clauses                  : 616
% 0.42/0.60  # Current number of unprocessed clauses: 11842
% 0.42/0.60  # ...number of literals in the above   : 44155
% 0.42/0.60  # Current number of archived formulas  : 0
% 0.42/0.60  # Current number of archived clauses   : 43
% 0.42/0.60  # Clause-clause subsumption calls (NU) : 37499
% 0.42/0.60  # Rec. Clause-clause subsumption calls : 18236
% 0.42/0.60  # Non-unit clause-clause subsumptions  : 680
% 0.42/0.60  # Unit Clause-clause subsumption calls : 2739
% 0.42/0.60  # Rewrite failures with RHS unbound    : 0
% 0.42/0.60  # BW rewrite match attempts            : 165
% 0.42/0.60  # BW rewrite match successes           : 6
% 0.42/0.60  # Condensation attempts                : 0
% 0.42/0.60  # Condensation successes               : 0
% 0.42/0.60  # Termbank termtop insertions          : 419869
% 0.42/0.60  
% 0.42/0.60  # -------------------------------------------------
% 0.42/0.60  # User time                : 0.242 s
% 0.42/0.60  # System time              : 0.010 s
% 0.42/0.60  # Total time               : 0.253 s
% 0.42/0.60  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
