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
% DateTime   : Thu Dec  3 10:53:57 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 164 expanded)
%              Number of clauses        :   33 (  61 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  152 ( 568 expanded)
%              Number of equality atoms :   61 ( 213 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
          & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(t199_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( k2_relat_1(X1) = k2_relat_1(X2)
               => k2_relat_1(k5_relat_1(X1,X3)) = k2_relat_1(k5_relat_1(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(t198_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( k1_relat_1(X1) = k1_relat_1(X2)
               => k1_relat_1(k5_relat_1(X3,X1)) = k1_relat_1(k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
            & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_funct_1])).

fof(c_0_11,plain,(
    ! [X8,X9,X10] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | k2_relat_1(X8) != k2_relat_1(X9)
      | k2_relat_1(k5_relat_1(X8,X10)) = k2_relat_1(k5_relat_1(X9,X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t199_relat_1])])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0)
    & ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0)
      | k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_13,plain,
    ( k2_relat_1(k5_relat_1(X1,X3)) = k2_relat_1(k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X1) != k2_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X4] : v1_relat_1(k6_relat_1(X4)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_16,plain,(
    ! [X11] :
      ( k1_relat_1(k6_relat_1(X11)) = X11
      & k2_relat_1(k6_relat_1(X11)) = X11 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_17,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,esk1_0)) = k2_relat_1(k5_relat_1(X2,esk1_0))
    | k2_relat_1(X1) != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k7_relat_1(X14,X13) = k5_relat_1(k6_relat_1(X13),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_21,plain,(
    ! [X16] :
      ( ( v1_relat_1(k2_funct_1(X16))
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( v1_funct_1(k2_funct_1(X16))
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_22,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X1)),esk1_0)) = k2_relat_1(k5_relat_1(X1,esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_23,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,k2_relat_1(X1))) = k2_relat_1(k5_relat_1(X1,esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_14])])).

fof(c_0_26,plain,(
    ! [X17] :
      ( ( k2_relat_1(X17) = k1_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( k1_relat_1(X17) = k2_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_27,plain,(
    ! [X5,X6,X7] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | k1_relat_1(X5) != k1_relat_1(X6)
      | k1_relat_1(k5_relat_1(X7,X5)) = k1_relat_1(k5_relat_1(X7,X6)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t198_relat_1])])])).

cnf(c_0_28,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,esk1_0)) = k2_relat_1(k5_relat_1(k2_funct_1(X2),esk1_0))
    | k2_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0)) = k2_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_18])])).

cnf(c_0_30,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( k1_relat_1(k5_relat_1(X3,X1)) = k1_relat_1(k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k1_relat_1(X1) != k1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,k2_relat_1(k2_funct_1(X1)))) = k2_relat_1(k5_relat_1(k2_funct_1(X1),esk1_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_29]),c_0_18])])])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_14])])).

fof(c_0_36,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k7_relat_1(X15,k1_relat_1(X15)) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_37,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X2)) = k1_relat_1(k5_relat_1(k2_funct_1(X1),X3))
    | k1_relat_1(X2) != k1_relat_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_24])).

fof(c_0_38,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k5_relat_1(X12,k6_relat_1(k2_relat_1(X12))) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,k1_relat_1(esk1_0))) = k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_32]),c_0_14])])).

cnf(c_0_40,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1)) = k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_32]),c_0_14])])).

cnf(c_0_42,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0)
    | k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) = k2_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_14])])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_18]),c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(esk1_0))) = k2_funct_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) = k1_relat_1(k2_funct_1(esk1_0))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_14])])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk1_0)) != k2_relat_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_51,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_31]),c_0_32]),c_0_14])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_24]),c_0_32]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.027 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t59_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)&k2_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 0.19/0.39  fof(t199_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(k2_relat_1(X1)=k2_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X3))=k2_relat_1(k5_relat_1(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 0.19/0.39  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.19/0.39  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.39  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.39  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.39  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.39  fof(t198_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(k1_relat_1(X1)=k1_relat_1(X2)=>k1_relat_1(k5_relat_1(X3,X1))=k1_relat_1(k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 0.19/0.39  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.19/0.39  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.19/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)&k2_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1))))), inference(assume_negation,[status(cth)],[t59_funct_1])).
% 0.19/0.39  fof(c_0_11, plain, ![X8, X9, X10]:(~v1_relat_1(X8)|(~v1_relat_1(X9)|(~v1_relat_1(X10)|(k2_relat_1(X8)!=k2_relat_1(X9)|k2_relat_1(k5_relat_1(X8,X10))=k2_relat_1(k5_relat_1(X9,X10)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t199_relat_1])])])).
% 0.19/0.39  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(v2_funct_1(esk1_0)&(k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)|k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.39  cnf(c_0_13, plain, (k2_relat_1(k5_relat_1(X1,X3))=k2_relat_1(k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|k2_relat_1(X1)!=k2_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  fof(c_0_15, plain, ![X4]:v1_relat_1(k6_relat_1(X4)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.19/0.39  fof(c_0_16, plain, ![X11]:(k1_relat_1(k6_relat_1(X11))=X11&k2_relat_1(k6_relat_1(X11))=X11), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.39  cnf(c_0_17, negated_conjecture, (k2_relat_1(k5_relat_1(X1,esk1_0))=k2_relat_1(k5_relat_1(X2,esk1_0))|k2_relat_1(X1)!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.39  cnf(c_0_18, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_19, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  fof(c_0_20, plain, ![X13, X14]:(~v1_relat_1(X14)|k7_relat_1(X14,X13)=k5_relat_1(k6_relat_1(X13),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.39  fof(c_0_21, plain, ![X16]:((v1_relat_1(k2_funct_1(X16))|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(v1_funct_1(k2_funct_1(X16))|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.39  cnf(c_0_22, negated_conjecture, (k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X1)),esk1_0))=k2_relat_1(k5_relat_1(X1,esk1_0))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.19/0.39  cnf(c_0_23, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_24, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,k2_relat_1(X1)))=k2_relat_1(k5_relat_1(X1,esk1_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_14])])).
% 0.19/0.39  fof(c_0_26, plain, ![X17]:((k2_relat_1(X17)=k1_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(k1_relat_1(X17)=k2_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.39  fof(c_0_27, plain, ![X5, X6, X7]:(~v1_relat_1(X5)|(~v1_relat_1(X6)|(~v1_relat_1(X7)|(k1_relat_1(X5)!=k1_relat_1(X6)|k1_relat_1(k5_relat_1(X7,X5))=k1_relat_1(k5_relat_1(X7,X6)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t198_relat_1])])])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (k2_relat_1(k5_relat_1(X1,esk1_0))=k2_relat_1(k5_relat_1(k2_funct_1(X2),esk1_0))|k2_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_17, c_0_24])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (k2_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0))=k2_relat_1(k7_relat_1(esk1_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_19]), c_0_18])])).
% 0.19/0.39  cnf(c_0_30, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_33, plain, (k1_relat_1(k5_relat_1(X3,X1))=k1_relat_1(k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|k1_relat_1(X1)!=k1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,k2_relat_1(k2_funct_1(X1))))=k2_relat_1(k5_relat_1(k2_funct_1(X1),esk1_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_19]), c_0_29]), c_0_18])])])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (k2_relat_1(k2_funct_1(esk1_0))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_14])])).
% 0.19/0.39  fof(c_0_36, plain, ![X15]:(~v1_relat_1(X15)|k7_relat_1(X15,k1_relat_1(X15))=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.19/0.39  cnf(c_0_37, plain, (k1_relat_1(k5_relat_1(k2_funct_1(X1),X2))=k1_relat_1(k5_relat_1(k2_funct_1(X1),X3))|k1_relat_1(X2)!=k1_relat_1(X3)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_24])).
% 0.19/0.39  fof(c_0_38, plain, ![X12]:(~v1_relat_1(X12)|k5_relat_1(X12,k6_relat_1(k2_relat_1(X12)))=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,k1_relat_1(esk1_0)))=k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_32]), c_0_14])])).
% 0.19/0.39  cnf(c_0_40, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1))=k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_32]), c_0_14])])).
% 0.19/0.39  cnf(c_0_42, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_43, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)|k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))=k2_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_14])])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(X1))))=k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_18]), c_0_42])])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(esk1_0)))=k2_funct_1(esk1_0)|~v1_relat_1(k2_funct_1(esk1_0))), inference(spm,[status(thm)],[c_0_43, c_0_35])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))=k1_relat_1(k2_funct_1(esk1_0))|~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_14])])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (k1_relat_1(k2_funct_1(esk1_0))!=k2_relat_1(esk1_0)|~v1_relat_1(k2_funct_1(esk1_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.39  cnf(c_0_51, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_31]), c_0_32]), c_0_14])])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_24]), c_0_32]), c_0_14])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 54
% 0.19/0.39  # Proof object clause steps            : 33
% 0.19/0.39  # Proof object formula steps           : 21
% 0.19/0.39  # Proof object conjectures             : 24
% 0.19/0.39  # Proof object clause conjectures      : 21
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 15
% 0.19/0.39  # Proof object initial formulas used   : 10
% 0.19/0.39  # Proof object generating inferences   : 17
% 0.19/0.39  # Proof object simplifying inferences  : 33
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 10
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 16
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 16
% 0.19/0.40  # Processed clauses                    : 256
% 0.19/0.40  # ...of these trivial                  : 1
% 0.19/0.40  # ...subsumed                          : 115
% 0.19/0.40  # ...remaining for further processing  : 140
% 0.19/0.40  # Other redundant clauses eliminated   : 15
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 5
% 0.19/0.40  # Backward-rewritten                   : 6
% 0.19/0.40  # Generated clauses                    : 1084
% 0.19/0.40  # ...of the previous two non-trivial   : 1051
% 0.19/0.40  # Contextual simplify-reflections      : 9
% 0.19/0.40  # Paramodulations                      : 1067
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 17
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
% 0.19/0.40  # Current number of processed clauses  : 113
% 0.19/0.40  #    Positive orientable unit clauses  : 16
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 95
% 0.19/0.40  # Current number of unprocessed clauses: 821
% 0.19/0.40  # ...number of literals in the above   : 3834
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 27
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 790
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 511
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 127
% 0.19/0.40  # Unit Clause-clause subsumption calls : 37
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 12
% 0.19/0.40  # BW rewrite match successes           : 6
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 29256
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.056 s
% 0.19/0.40  # System time              : 0.003 s
% 0.19/0.40  # Total time               : 0.059 s
% 0.19/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
