%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:40 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  64 expanded)
%              Number of clauses        :   21 (  25 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  111 ( 224 expanded)
%              Number of equality atoms :   34 (  55 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_zfmisc_1(X2) )
           => ( r1_tarski(X1,X2)
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t1_tex_2])).

fof(c_0_9,plain,(
    ! [X30,X31] :
      ( v1_xboole_0(X30)
      | ~ m1_subset_1(X31,X30)
      | k6_domain_1(X30,X31) = k1_tarski(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_10,plain,(
    ! [X32,X34] :
      ( ( m1_subset_1(esk1_1(X32),X32)
        | ~ v1_zfmisc_1(X32)
        | v1_xboole_0(X32) )
      & ( X32 = k6_domain_1(X32,esk1_1(X32))
        | ~ v1_zfmisc_1(X32)
        | v1_xboole_0(X32) )
      & ( ~ m1_subset_1(X34,X32)
        | X32 != k6_domain_1(X32,X34)
        | v1_zfmisc_1(X32)
        | v1_xboole_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

fof(c_0_11,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | r1_tarski(X12,k2_xboole_0(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_12,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & v1_zfmisc_1(esk3_0)
    & r1_tarski(esk2_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_13,plain,(
    ! [X28,X29] :
      ( ( ~ r1_tarski(X28,k1_tarski(X29))
        | X28 = k1_xboole_0
        | X28 = k1_tarski(X29) )
      & ( X28 != k1_xboole_0
        | r1_tarski(X28,k1_tarski(X29)) )
      & ( X28 != k1_tarski(X29)
        | r1_tarski(X28,k1_tarski(X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X25)
      | ~ r1_tarski(X25,X24)
      | ~ r1_xboole_0(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_tarski(esk1_1(X1)) = k6_domain_1(X1,esk1_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_22,plain,(
    ! [X26,X27] :
      ( ( ~ r1_xboole_0(X26,X27)
        | k4_xboole_0(X26,X27) = X26 )
      & ( k4_xboole_0(X26,X27) != X26
        | r1_xboole_0(X26,X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( X1 = k6_domain_1(X2,esk1_1(X2))
    | X1 = k1_xboole_0
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,k6_domain_1(X2,esk1_1(X2))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( X1 = k6_domain_1(X1,esk1_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(X1,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k2_xboole_0(X1,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_26])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X1 = X2
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v1_zfmisc_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_33])]),c_0_34]),c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:33:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S083N
% 0.19/0.40  # and selection function SelectCQArNT.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.028 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t1_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.19/0.40  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.40  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 0.19/0.40  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.19/0.40  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.19/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.40  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.19/0.40  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.40  fof(c_0_8, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2)))), inference(assume_negation,[status(cth)],[t1_tex_2])).
% 0.19/0.40  fof(c_0_9, plain, ![X30, X31]:(v1_xboole_0(X30)|~m1_subset_1(X31,X30)|k6_domain_1(X30,X31)=k1_tarski(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.40  fof(c_0_10, plain, ![X32, X34]:(((m1_subset_1(esk1_1(X32),X32)|~v1_zfmisc_1(X32)|v1_xboole_0(X32))&(X32=k6_domain_1(X32,esk1_1(X32))|~v1_zfmisc_1(X32)|v1_xboole_0(X32)))&(~m1_subset_1(X34,X32)|X32!=k6_domain_1(X32,X34)|v1_zfmisc_1(X32)|v1_xboole_0(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.19/0.40  fof(c_0_11, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|r1_tarski(X12,k2_xboole_0(X14,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.19/0.40  fof(c_0_12, negated_conjecture, (~v1_xboole_0(esk2_0)&((~v1_xboole_0(esk3_0)&v1_zfmisc_1(esk3_0))&(r1_tarski(esk2_0,esk3_0)&esk2_0!=esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.19/0.40  fof(c_0_13, plain, ![X28, X29]:((~r1_tarski(X28,k1_tarski(X29))|(X28=k1_xboole_0|X28=k1_tarski(X29)))&((X28!=k1_xboole_0|r1_tarski(X28,k1_tarski(X29)))&(X28!=k1_tarski(X29)|r1_tarski(X28,k1_tarski(X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.19/0.40  cnf(c_0_14, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_15, plain, (m1_subset_1(esk1_1(X1),X1)|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_16, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.40  cnf(c_0_17, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  fof(c_0_19, plain, ![X24, X25]:(v1_xboole_0(X25)|(~r1_tarski(X25,X24)|~r1_xboole_0(X25,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.19/0.40  cnf(c_0_20, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_21, plain, (k1_tarski(esk1_1(X1))=k6_domain_1(X1,esk1_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.40  fof(c_0_22, plain, ![X26, X27]:((~r1_xboole_0(X26,X27)|k4_xboole_0(X26,X27)=X26)&(k4_xboole_0(X26,X27)!=X26|r1_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.40  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.40  cnf(c_0_25, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_27, plain, (X1=k6_domain_1(X2,esk1_1(X2))|X1=k1_xboole_0|v1_xboole_0(X2)|~v1_zfmisc_1(X2)|~r1_tarski(X1,k6_domain_1(X2,esk1_1(X2)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  cnf(c_0_28, plain, (X1=k6_domain_1(X1,esk1_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(X1,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (~r1_xboole_0(esk2_0,k2_xboole_0(X1,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_26])).
% 0.19/0.40  cnf(c_0_32, plain, (X1=k1_xboole_0|X1=X2|v1_xboole_0(X2)|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (v1_zfmisc_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (esk2_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_33])]), c_0_34]), c_0_35]), c_0_36]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 38
% 0.19/0.40  # Proof object clause steps            : 21
% 0.19/0.40  # Proof object formula steps           : 17
% 0.19/0.40  # Proof object conjectures             : 13
% 0.19/0.40  # Proof object clause conjectures      : 10
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 13
% 0.19/0.40  # Proof object initial formulas used   : 8
% 0.19/0.40  # Proof object generating inferences   : 8
% 0.19/0.40  # Proof object simplifying inferences  : 7
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 16
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 28
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 28
% 0.19/0.40  # Processed clauses                    : 1447
% 0.19/0.40  # ...of these trivial                  : 89
% 0.19/0.40  # ...subsumed                          : 1104
% 0.19/0.40  # ...remaining for further processing  : 254
% 0.19/0.40  # Other redundant clauses eliminated   : 9
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 2
% 0.19/0.40  # Backward-rewritten                   : 6
% 0.19/0.40  # Generated clauses                    : 3958
% 0.19/0.40  # ...of the previous two non-trivial   : 2342
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 3949
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 9
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 216
% 0.19/0.40  #    Positive orientable unit clauses  : 87
% 0.19/0.40  #    Positive unorientable unit clauses: 1
% 0.19/0.40  #    Negative unit clauses             : 48
% 0.19/0.40  #    Non-unit-clauses                  : 80
% 0.19/0.40  # Current number of unprocessed clauses: 943
% 0.19/0.40  # ...number of literals in the above   : 1329
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 34
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 1278
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1126
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 185
% 0.19/0.40  # Unit Clause-clause subsumption calls : 873
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 161
% 0.19/0.40  # BW rewrite match successes           : 19
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 33761
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.067 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.072 s
% 0.19/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
