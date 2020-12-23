%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0648+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:49 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   18 (  53 expanded)
%              Number of clauses        :   11 (  18 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   47 ( 192 expanded)
%              Number of equality atoms :   20 (  76 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t37_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
            & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t55_funct_1])).

fof(c_0_4,plain,(
    ! [X2737] :
      ( ~ v1_relat_1(X2737)
      | ~ v1_funct_1(X2737)
      | ~ v2_funct_1(X2737)
      | k2_funct_1(X2737) = k4_relat_1(X2737) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk193_0)
    & v1_funct_1(esk193_0)
    & v2_funct_1(esk193_0)
    & ( k2_relat_1(esk193_0) != k1_relat_1(k2_funct_1(esk193_0))
      | k1_relat_1(esk193_0) != k2_relat_1(k2_funct_1(esk193_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X2614] :
      ( ( k2_relat_1(X2614) = k1_relat_1(k4_relat_1(X2614))
        | ~ v1_relat_1(X2614) )
      & ( k1_relat_1(X2614) = k2_relat_1(k4_relat_1(X2614))
        | ~ v1_relat_1(X2614) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_7,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_1(esk193_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v2_funct_1(esk193_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk193_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( k2_relat_1(esk193_0) != k1_relat_1(k2_funct_1(esk193_0))
    | k1_relat_1(esk193_0) != k2_relat_1(k2_funct_1(esk193_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( k2_funct_1(esk193_0) = k4_relat_1(esk193_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_15,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk193_0)) = k2_relat_1(esk193_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk193_0)) = k1_relat_1(esk193_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_14]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
