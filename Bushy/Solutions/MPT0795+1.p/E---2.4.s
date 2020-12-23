%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t47_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:14 EDT 2019

% Result     : Theorem 151.26s
% Output     : CNFRefutation 151.26s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 251 expanded)
%              Number of clauses        :   33 ( 109 expanded)
%              Number of leaves         :    8 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  279 (1554 expanded)
%              Number of equality atoms :   41 ( 263 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   90 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
              <=> ( k1_relat_1(X3) = k3_relat_1(X1)
                  & k2_relat_1(X3) = k3_relat_1(X2)
                  & v2_funct_1(X3)
                  & ! [X4,X5] :
                      ( r2_hidden(k4_tarski(X4,X5),X1)
                    <=> ( r2_hidden(X4,k3_relat_1(X1))
                        & r2_hidden(X5,k3_relat_1(X1))
                        & r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',d7_wellord1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t30_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',fc4_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',fc3_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',dt_k6_relat_1)).

fof(t35_funct_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t35_funct_1)).

fof(t47_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t47_wellord1.p',t47_wellord1)).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( k1_relat_1(X13) = k3_relat_1(X11)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X13) = k3_relat_1(X12)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( v2_funct_1(X13)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(X14,k3_relat_1(X11))
        | ~ r2_hidden(k4_tarski(X14,X15),X11)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(X15,k3_relat_1(X11))
        | ~ r2_hidden(k4_tarski(X14,X15),X11)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X13,X14),k1_funct_1(X13,X15)),X12)
        | ~ r2_hidden(k4_tarski(X14,X15),X11)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X16,k3_relat_1(X11))
        | ~ r2_hidden(X17,k3_relat_1(X11))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X13,X16),k1_funct_1(X13,X17)),X12)
        | r2_hidden(k4_tarski(X16,X17),X11)
        | ~ r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X11,X12,X13),esk3_3(X11,X12,X13)),X11)
        | ~ r2_hidden(esk2_3(X11,X12,X13),k3_relat_1(X11))
        | ~ r2_hidden(esk3_3(X11,X12,X13),k3_relat_1(X11))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X13,esk2_3(X11,X12,X13)),k1_funct_1(X13,esk3_3(X11,X12,X13))),X12)
        | k1_relat_1(X13) != k3_relat_1(X11)
        | k2_relat_1(X13) != k3_relat_1(X12)
        | ~ v2_funct_1(X13)
        | r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),k3_relat_1(X11))
        | r2_hidden(k4_tarski(esk2_3(X11,X12,X13),esk3_3(X11,X12,X13)),X11)
        | k1_relat_1(X13) != k3_relat_1(X11)
        | k2_relat_1(X13) != k3_relat_1(X12)
        | ~ v2_funct_1(X13)
        | r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk3_3(X11,X12,X13),k3_relat_1(X11))
        | r2_hidden(k4_tarski(esk2_3(X11,X12,X13),esk3_3(X11,X12,X13)),X11)
        | k1_relat_1(X13) != k3_relat_1(X11)
        | k2_relat_1(X13) != k3_relat_1(X12)
        | ~ v2_funct_1(X13)
        | r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X13,esk2_3(X11,X12,X13)),k1_funct_1(X13,esk3_3(X11,X12,X13))),X12)
        | r2_hidden(k4_tarski(esk2_3(X11,X12,X13),esk3_3(X11,X12,X13)),X11)
        | k1_relat_1(X13) != k3_relat_1(X11)
        | k2_relat_1(X13) != k3_relat_1(X12)
        | ~ v2_funct_1(X13)
        | r3_wellord1(X11,X12,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_wellord1])])])])])])).

fof(c_0_9,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(X29,k3_relat_1(X31))
        | ~ r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(X30,k3_relat_1(X31))
        | ~ r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k3_relat_1(X1))
    | r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)
    | r3_wellord1(X1,X2,X3)
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X35] :
      ( k1_relat_1(k6_relat_1(X35)) = X35
      & k2_relat_1(k6_relat_1(X35)) = X35 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_13,plain,(
    ! [X41] :
      ( v1_relat_1(k6_relat_1(X41))
      & v2_funct_1(k6_relat_1(X41)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_14,plain,(
    ! [X40] :
      ( v1_relat_1(k6_relat_1(X40))
      & v1_funct_1(k6_relat_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_15,plain,(
    ! [X20] : v1_relat_1(k6_relat_1(X20)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k3_relat_1(X1))
    | r3_wellord1(X1,X2,X3)
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k3_relat_1(X1))
    | r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)
    | r3_wellord1(X1,X2,X3)
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(X1,esk2_3(X2,X3,X1)),k1_funct_1(X1,esk3_3(X2,X3,X1))),X3)
    | r2_hidden(k4_tarski(esk2_3(X2,X3,X1),esk3_3(X2,X3,X1)),X2)
    | r3_wellord1(X2,X3,X1)
    | k1_relat_1(X1) != k3_relat_1(X2)
    | k2_relat_1(X1) != k3_relat_1(X3)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_25,plain,(
    ! [X32,X33] :
      ( ~ r2_hidden(X32,X33)
      | k1_funct_1(k6_relat_1(X33),X32) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).

cnf(c_0_26,plain,
    ( r2_hidden(esk3_3(X1,X2,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k3_relat_1(X1))
    | r3_wellord1(X1,X2,X3)
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r3_wellord1(X1,X2,X3)
    | ~ r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),k3_relat_1(X1))
    | ~ r2_hidden(esk3_3(X1,X2,X3),k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(k1_funct_1(X3,esk2_3(X1,X2,X3)),k1_funct_1(X3,esk3_3(X1,X2,X3))),X2)
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk3_3(X1,X2,k6_relat_1(k3_relat_1(X1))))),X2)
    | r2_hidden(k4_tarski(esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk3_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X1)
    | r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])])])).

cnf(c_0_30,plain,
    ( k1_funct_1(k6_relat_1(X2),X1) = X1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])])])).

cnf(c_0_33,plain,
    ( r3_wellord1(X1,X2,X3)
    | k1_relat_1(X3) != k3_relat_1(X1)
    | k2_relat_1(X3) != k3_relat_1(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(k4_tarski(k1_funct_1(X3,esk2_3(X1,X2,X3)),k1_funct_1(X3,esk3_3(X1,X2,X3))),X2)
    | ~ r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_28,c_0_11]),c_0_23])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1))))),X1)
    | r2_hidden(k4_tarski(esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1))),esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),X1)
    | r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1)))) = esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1))),k3_relat_1(X1))
    | r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( r3_wellord1(X1,X2,k6_relat_1(k3_relat_1(X1)))
    | k3_relat_1(X1) != k3_relat_1(X2)
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk3_3(X1,X2,k6_relat_1(k3_relat_1(X1))))),X2)
    | ~ r2_hidden(k4_tarski(esk2_3(X1,X2,k6_relat_1(k3_relat_1(X1))),esk3_3(X1,X2,k6_relat_1(k3_relat_1(X1)))),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])])])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),X1)
    | r2_hidden(k4_tarski(esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1))),esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),X1)
    | r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1)))) = esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_40,plain,
    ( r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1))))),X1)
    | ~ r2_hidden(k4_tarski(esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1))),esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1))),esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),X1)
    | r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1))) ) ),
    inference(assume_negation,[status(cth)],[t47_wellord1])).

cnf(c_0_43,plain,
    ( r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1))))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_44,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & ~ r3_wellord1(esk1_0,esk1_0,k6_relat_1(k3_relat_1(esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

cnf(c_0_45,plain,
    ( r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),esk2_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),esk3_3(X1,X1,k6_relat_1(k3_relat_1(X1)))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( ~ r3_wellord1(esk1_0,esk1_0,k6_relat_1(k3_relat_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_47,plain,
    ( r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_39]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
