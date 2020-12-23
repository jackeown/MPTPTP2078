%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t60_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:25 EDT 2019

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 263 expanded)
%              Number of clauses        :   29 (  91 expanded)
%              Number of leaves         :    5 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  356 (2853 expanded)
%              Number of equality atoms :  117 (1004 expanded)
%              Maximal formula depth    :   31 (   7 average)
%              Maximal clause size      :  130 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t54_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( X2 = k2_funct_1(X1)
            <=> ( k1_relat_1(X2) = k2_relat_1(X1)
                & ! [X3,X4] :
                    ( ( ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) )
                     => ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) ) )
                    & ( ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) )
                     => ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t60_funct_1.p',t54_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t60_funct_1.p',dt_k2_funct_1)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t60_funct_1.p',t9_funct_1)).

fof(t60_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k1_relat_1(X1) = k2_relat_1(X2)
              & k2_relat_1(X1) = k1_relat_1(X2)
              & ! [X3,X4] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X4,k1_relat_1(X2)) )
                 => ( k1_funct_1(X1,X3) = X4
                  <=> k1_funct_1(X2,X4) = X3 ) ) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t60_funct_1.p',t60_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t60_funct_1.p',d5_funct_1)).

fof(c_0_5,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( k1_relat_1(X29) = k2_relat_1(X28)
        | X29 != k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( r2_hidden(X31,k1_relat_1(X28))
        | ~ r2_hidden(X30,k2_relat_1(X28))
        | X31 != k1_funct_1(X29,X30)
        | X29 != k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( X30 = k1_funct_1(X28,X31)
        | ~ r2_hidden(X30,k2_relat_1(X28))
        | X31 != k1_funct_1(X29,X30)
        | X29 != k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( r2_hidden(X32,k2_relat_1(X28))
        | ~ r2_hidden(X33,k1_relat_1(X28))
        | X32 != k1_funct_1(X28,X33)
        | X29 != k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( X33 = k1_funct_1(X29,X32)
        | ~ r2_hidden(X33,k1_relat_1(X28))
        | X32 != k1_funct_1(X28,X33)
        | X29 != k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( r2_hidden(esk10_2(X28,X29),k1_relat_1(X28))
        | r2_hidden(esk7_2(X28,X29),k2_relat_1(X28))
        | k1_relat_1(X29) != k2_relat_1(X28)
        | X29 = k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( esk9_2(X28,X29) = k1_funct_1(X28,esk10_2(X28,X29))
        | r2_hidden(esk7_2(X28,X29),k2_relat_1(X28))
        | k1_relat_1(X29) != k2_relat_1(X28)
        | X29 = k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( ~ r2_hidden(esk9_2(X28,X29),k2_relat_1(X28))
        | esk10_2(X28,X29) != k1_funct_1(X29,esk9_2(X28,X29))
        | r2_hidden(esk7_2(X28,X29),k2_relat_1(X28))
        | k1_relat_1(X29) != k2_relat_1(X28)
        | X29 = k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( r2_hidden(esk10_2(X28,X29),k1_relat_1(X28))
        | esk8_2(X28,X29) = k1_funct_1(X29,esk7_2(X28,X29))
        | k1_relat_1(X29) != k2_relat_1(X28)
        | X29 = k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( esk9_2(X28,X29) = k1_funct_1(X28,esk10_2(X28,X29))
        | esk8_2(X28,X29) = k1_funct_1(X29,esk7_2(X28,X29))
        | k1_relat_1(X29) != k2_relat_1(X28)
        | X29 = k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( ~ r2_hidden(esk9_2(X28,X29),k2_relat_1(X28))
        | esk10_2(X28,X29) != k1_funct_1(X29,esk9_2(X28,X29))
        | esk8_2(X28,X29) = k1_funct_1(X29,esk7_2(X28,X29))
        | k1_relat_1(X29) != k2_relat_1(X28)
        | X29 = k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( r2_hidden(esk10_2(X28,X29),k1_relat_1(X28))
        | ~ r2_hidden(esk8_2(X28,X29),k1_relat_1(X28))
        | esk7_2(X28,X29) != k1_funct_1(X28,esk8_2(X28,X29))
        | k1_relat_1(X29) != k2_relat_1(X28)
        | X29 = k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( esk9_2(X28,X29) = k1_funct_1(X28,esk10_2(X28,X29))
        | ~ r2_hidden(esk8_2(X28,X29),k1_relat_1(X28))
        | esk7_2(X28,X29) != k1_funct_1(X28,esk8_2(X28,X29))
        | k1_relat_1(X29) != k2_relat_1(X28)
        | X29 = k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( ~ r2_hidden(esk9_2(X28,X29),k2_relat_1(X28))
        | esk10_2(X28,X29) != k1_funct_1(X29,esk9_2(X28,X29))
        | ~ r2_hidden(esk8_2(X28,X29),k1_relat_1(X28))
        | esk7_2(X28,X29) != k1_funct_1(X28,esk8_2(X28,X29))
        | k1_relat_1(X29) != k2_relat_1(X28)
        | X29 = k2_funct_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

fof(c_0_6,plain,(
    ! [X21] :
      ( ( v1_relat_1(k2_funct_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( v1_funct_1(k2_funct_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_7,plain,(
    ! [X43,X44] :
      ( ( r2_hidden(esk11_2(X43,X44),k1_relat_1(X43))
        | k1_relat_1(X43) != k1_relat_1(X44)
        | X43 = X44
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) )
      & ( k1_funct_1(X43,esk11_2(X43,X44)) != k1_funct_1(X44,esk11_2(X43,X44))
        | k1_relat_1(X43) != k1_relat_1(X44)
        | X43 = X44
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_8,plain,
    ( k1_relat_1(X1) = k2_relat_1(X2)
    | X1 != k2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & k1_relat_1(X1) = k2_relat_1(X2)
                & k2_relat_1(X1) = k1_relat_1(X2)
                & ! [X3,X4] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X4,k1_relat_1(X2)) )
                   => ( k1_funct_1(X1,X3) = X4
                    <=> k1_funct_1(X2,X4) = X3 ) ) )
             => X2 = k2_funct_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t60_funct_1])).

cnf(c_0_12,plain,
    ( r2_hidden(esk11_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k1_relat_1(k2_funct_1(X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]),c_0_9]),c_0_10])).

fof(c_0_14,negated_conjecture,(
    ! [X7,X8] :
      ( v1_relat_1(esk1_0)
      & v1_funct_1(esk1_0)
      & v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & v2_funct_1(esk1_0)
      & k1_relat_1(esk1_0) = k2_relat_1(esk2_0)
      & k2_relat_1(esk1_0) = k1_relat_1(esk2_0)
      & ( k1_funct_1(esk1_0,X7) != X8
        | k1_funct_1(esk2_0,X8) = X7
        | ~ r2_hidden(X7,k1_relat_1(esk1_0))
        | ~ r2_hidden(X8,k1_relat_1(esk2_0)) )
      & ( k1_funct_1(esk2_0,X8) != X7
        | k1_funct_1(esk1_0,X7) = X8
        | ~ r2_hidden(X7,k1_relat_1(esk1_0))
        | ~ r2_hidden(X8,k1_relat_1(esk2_0)) )
      & esk2_0 != k2_funct_1(esk1_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).

fof(c_0_15,plain,(
    ! [X11,X12,X13,X15,X16,X17,X19] :
      ( ( r2_hidden(esk3_3(X11,X12,X13),k1_relat_1(X11))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X13 = k1_funct_1(X11,esk3_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X16,k1_relat_1(X11))
        | X15 != k1_funct_1(X11,X16)
        | r2_hidden(X15,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk4_2(X11,X17),X17)
        | ~ r2_hidden(X19,k1_relat_1(X11))
        | esk4_2(X11,X17) != k1_funct_1(X11,X19)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk5_2(X11,X17),k1_relat_1(X11))
        | r2_hidden(esk4_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk4_2(X11,X17) = k1_funct_1(X11,esk5_2(X11,X17))
        | r2_hidden(esk4_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_16,plain,
    ( k2_funct_1(X1) = X2
    | r2_hidden(esk11_2(k2_funct_1(X1),X2),k2_relat_1(X1))
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_9]),c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k2_funct_1(esk1_0) = X1
    | r2_hidden(esk11_2(k2_funct_1(esk1_0),X1),k1_relat_1(esk2_0))
    | k1_relat_1(esk2_0) != k1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( esk2_0 != k2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( k1_funct_1(esk1_0,X2) = X1
    | k1_funct_1(esk2_0,X1) != X2
    | ~ r2_hidden(X2,k1_relat_1(esk1_0))
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk11_2(k2_funct_1(esk1_0),esk2_0),k1_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(esk1_0) = k2_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk11_2(X1,X2)) != k1_funct_1(X2,esk11_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(X1,k1_relat_1(X4))
    | X3 != k1_funct_1(X4,X1)
    | X2 != k2_funct_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X4)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk1_0,k1_funct_1(esk2_0,X1)) = X1
    | ~ r2_hidden(k1_funct_1(esk2_0,X1),k1_relat_1(esk1_0))
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk2_0,esk11_2(k2_funct_1(esk1_0),esk2_0)),k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_23]),c_0_24])])).

cnf(c_0_34,plain,
    ( k2_funct_1(X1) = X2
    | k1_funct_1(k2_funct_1(X1),esk11_2(k2_funct_1(X1),X2)) != k1_funct_1(X2,esk11_2(k2_funct_1(X1),X2))
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_9]),c_0_10])).

cnf(c_0_35,plain,
    ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2)) = X2
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_31])]),c_0_9]),c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk1_0,k1_funct_1(esk2_0,esk11_2(k2_funct_1(esk1_0),esk2_0))) = esk11_2(k2_funct_1(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_33])])).

cnf(c_0_37,negated_conjecture,
    ( k2_funct_1(esk1_0) = X1
    | k1_funct_1(k2_funct_1(esk1_0),esk11_2(k2_funct_1(esk1_0),X1)) != k1_funct_1(X1,esk11_2(k2_funct_1(esk1_0),X1))
    | k1_relat_1(esk2_0) != k1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk1_0),esk11_2(k2_funct_1(esk1_0),esk2_0)) = k1_funct_1(esk2_0,esk11_2(k2_funct_1(esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_18]),c_0_19]),c_0_20])]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_38]),c_0_23]),c_0_24])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
