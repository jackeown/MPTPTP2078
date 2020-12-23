%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:32 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   32 (  57 expanded)
%              Number of clauses        :   19 (  21 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   96 ( 257 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_orders_2,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v6_orders_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X3,X2)
               => ( v6_orders_2(X3,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_orders_2)).

fof(t96_orders_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r7_relat_2(X3,X1)
          & r1_tarski(X2,X1) )
       => r7_relat_2(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_orders_1)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( ( v6_orders_2(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X3,X2)
                 => ( v6_orders_2(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_orders_2])).

fof(c_0_7,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ r7_relat_2(X13,X11)
      | ~ r1_tarski(X12,X11)
      | r7_relat_2(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_orders_1])])).

fof(c_0_8,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & v6_orders_2(esk2_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & r1_tarski(esk3_0,esk2_0)
    & ( ~ v6_orders_2(esk3_0,esk1_0)
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( r7_relat_2(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r7_relat_2(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( ~ v6_orders_2(X9,X8)
        | r7_relat_2(u1_orders_2(X8),X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_orders_2(X8) )
      & ( ~ r7_relat_2(u1_orders_2(X8),X9)
        | v6_orders_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

fof(c_0_12,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | m1_subset_1(u1_orders_2(X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X10)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_13,negated_conjecture,
    ( r7_relat_2(X1,esk3_0)
    | ~ r7_relat_2(X1,esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r7_relat_2(u1_orders_2(X2),X1)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | v1_relat_1(X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_18,plain,(
    ! [X6,X7] : v1_relat_1(k2_zfmisc_1(X6,X7)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_19,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r7_relat_2(u1_orders_2(X1),esk3_0)
    | ~ v6_orders_2(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_relat_1(u1_orders_2(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ v6_orders_2(esk3_0,esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( v6_orders_2(esk3_0,X1)
    | ~ v6_orders_2(esk2_0,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_relat_1(u1_orders_2(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v6_orders_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_30,negated_conjecture,
    ( ~ v6_orders_2(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_17]),c_0_25]),c_0_28]),c_0_29])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S028I
% 0.12/0.37  # and selection function SelectNonRROptimalLit.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.026 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t37_orders_2, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:((v6_orders_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_orders_2)).
% 0.12/0.37  fof(t96_orders_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r7_relat_2(X3,X1)&r1_tarski(X2,X1))=>r7_relat_2(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_orders_1)).
% 0.12/0.37  fof(d11_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_orders_2(X2,X1)<=>r7_relat_2(u1_orders_2(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 0.12/0.37  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.12/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.12/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.12/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:((v6_orders_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))))))), inference(assume_negation,[status(cth)],[t37_orders_2])).
% 0.12/0.37  fof(c_0_7, plain, ![X11, X12, X13]:(~v1_relat_1(X13)|(~r7_relat_2(X13,X11)|~r1_tarski(X12,X11)|r7_relat_2(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_orders_1])])).
% 0.12/0.37  fof(c_0_8, negated_conjecture, (l1_orders_2(esk1_0)&((v6_orders_2(esk2_0,esk1_0)&m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(r1_tarski(esk3_0,esk2_0)&(~v6_orders_2(esk3_0,esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.12/0.37  cnf(c_0_9, plain, (r7_relat_2(X1,X3)|~v1_relat_1(X1)|~r7_relat_2(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_11, plain, ![X8, X9]:((~v6_orders_2(X9,X8)|r7_relat_2(u1_orders_2(X8),X9)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_orders_2(X8))&(~r7_relat_2(u1_orders_2(X8),X9)|v6_orders_2(X9,X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_orders_2(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X10]:(~l1_orders_2(X10)|m1_subset_1(u1_orders_2(X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X10))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (r7_relat_2(X1,esk3_0)|~r7_relat_2(X1,esk2_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.37  cnf(c_0_14, plain, (r7_relat_2(u1_orders_2(X2),X1)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_15, plain, ![X4, X5]:(~v1_relat_1(X4)|(~m1_subset_1(X5,k1_zfmisc_1(X4))|v1_relat_1(X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.12/0.37  cnf(c_0_16, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_18, plain, ![X6, X7]:v1_relat_1(k2_zfmisc_1(X6,X7)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.12/0.37  cnf(c_0_19, plain, (v6_orders_2(X2,X1)|~r7_relat_2(u1_orders_2(X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (r7_relat_2(u1_orders_2(X1),esk3_0)|~v6_orders_2(esk2_0,X1)|~l1_orders_2(X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))|~v1_relat_1(u1_orders_2(X1))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_23, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (~v6_orders_2(esk3_0,esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (v6_orders_2(esk3_0,X1)|~v6_orders_2(esk2_0,X1)|~l1_orders_2(X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))|~v1_relat_1(u1_orders_2(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (v6_orders_2(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (v1_relat_1(u1_orders_2(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (~v6_orders_2(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_17]), c_0_25]), c_0_28]), c_0_29])]), c_0_30]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 32
% 0.12/0.37  # Proof object clause steps            : 19
% 0.12/0.37  # Proof object formula steps           : 13
% 0.12/0.37  # Proof object conjectures             : 16
% 0.12/0.37  # Proof object clause conjectures      : 13
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 12
% 0.12/0.37  # Proof object initial formulas used   : 6
% 0.12/0.37  # Proof object generating inferences   : 6
% 0.12/0.37  # Proof object simplifying inferences  : 10
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 6
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 12
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 12
% 0.12/0.37  # Processed clauses                    : 32
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 32
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 1
% 0.12/0.37  # Generated clauses                    : 9
% 0.12/0.37  # ...of the previous two non-trivial   : 8
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 9
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 19
% 0.12/0.37  #    Positive orientable unit clauses  : 8
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 10
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 13
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 47
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 6
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1117
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.002 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
