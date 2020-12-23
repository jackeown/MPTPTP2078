%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0652+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:49 EST 2020

% Result     : Timeout 58.92s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   48 ( 161 expanded)
%              Number of clauses        :   27 (  58 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  124 ( 561 expanded)
%              Number of equality atoms :   45 ( 207 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t160_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',dt_k4_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t37_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t146_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t169_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t182_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
            & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_funct_1])).

fof(c_0_11,plain,(
    ! [X2738] :
      ( ( v1_relat_1(k2_funct_1(X2738))
        | ~ v1_relat_1(X2738)
        | ~ v1_funct_1(X2738) )
      & ( v1_funct_1(k2_funct_1(X2738))
        | ~ v1_relat_1(X2738)
        | ~ v1_funct_1(X2738) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk193_0)
    & v1_funct_1(esk193_0)
    & v2_funct_1(esk193_0)
    & ( k1_relat_1(k5_relat_1(k2_funct_1(esk193_0),esk193_0)) != k2_relat_1(esk193_0)
      | k2_relat_1(k5_relat_1(k2_funct_1(esk193_0),esk193_0)) != k2_relat_1(esk193_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X2737] :
      ( ~ v1_relat_1(X2737)
      | ~ v1_funct_1(X2737)
      | ~ v2_funct_1(X2737)
      | k2_funct_1(X2737) = k4_relat_1(X2737) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_14,plain,(
    ! [X2432,X2433] :
      ( ~ v1_relat_1(X2432)
      | ~ v1_relat_1(X2433)
      | k2_relat_1(k5_relat_1(X2432,X2433)) = k9_relat_1(X2433,k2_relat_1(X2432)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

fof(c_0_15,plain,(
    ! [X2223] :
      ( ~ v1_relat_1(X2223)
      | v1_relat_1(k4_relat_1(X2223)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_16,plain,(
    ! [X2614] :
      ( ( k2_relat_1(X2614) = k1_relat_1(k4_relat_1(X2614))
        | ~ v1_relat_1(X2614) )
      & ( k1_relat_1(X2614) = k2_relat_1(k4_relat_1(X2614))
        | ~ v1_relat_1(X2614) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_17,plain,(
    ! [X2395] :
      ( ~ v1_relat_1(X2395)
      | k9_relat_1(X2395,k1_relat_1(X2395)) = k2_relat_1(X2395) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_18,plain,(
    ! [X2451] :
      ( ~ v1_relat_1(X2451)
      | k10_relat_1(X2451,k2_relat_1(X2451)) = k1_relat_1(X2451) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk193_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk193_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X2878] :
      ( ( k2_relat_1(X2878) = k1_relat_1(k2_funct_1(X2878))
        | ~ v2_funct_1(X2878)
        | ~ v1_relat_1(X2878)
        | ~ v1_funct_1(X2878) )
      & ( k1_relat_1(X2878) = k2_relat_1(k2_funct_1(X2878))
        | ~ v2_funct_1(X2878)
        | ~ v1_relat_1(X2878)
        | ~ v1_funct_1(X2878) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_23,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v2_funct_1(esk193_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_29,plain,(
    ! [X2482,X2483] :
      ( ~ v1_relat_1(X2482)
      | ~ v1_relat_1(X2483)
      | k1_relat_1(k5_relat_1(X2482,X2483)) = k10_relat_1(X2482,k1_relat_1(X2483)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_30,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk193_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_32,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk193_0),esk193_0)) != k2_relat_1(esk193_0)
    | k2_relat_1(k5_relat_1(k2_funct_1(esk193_0),esk193_0)) != k2_relat_1(esk193_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( k2_funct_1(esk193_0) = k4_relat_1(esk193_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_24]),c_0_21])])).

cnf(c_0_35,negated_conjecture,
    ( k9_relat_1(esk193_0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,esk193_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk193_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk193_0)) = k1_relat_1(esk193_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( k9_relat_1(esk193_0,k1_relat_1(esk193_0)) = k2_relat_1(esk193_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_39,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(k2_funct_1(esk193_0),k2_relat_1(k2_funct_1(esk193_0))) = k1_relat_1(k2_funct_1(esk193_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk193_0)) = k2_relat_1(esk193_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_24]),c_0_21])])).

cnf(c_0_42,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k4_relat_1(esk193_0),esk193_0)) != k2_relat_1(esk193_0)
    | k1_relat_1(k5_relat_1(k4_relat_1(esk193_0),esk193_0)) != k2_relat_1(esk193_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k4_relat_1(esk193_0),esk193_0)) = k2_relat_1(esk193_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k10_relat_1(X1,k1_relat_1(esk193_0)) = k1_relat_1(k5_relat_1(X1,esk193_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(k4_relat_1(esk193_0),k1_relat_1(esk193_0)) = k2_relat_1(esk193_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_34]),c_0_34]),c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k4_relat_1(esk193_0),esk193_0)) != k2_relat_1(esk193_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
