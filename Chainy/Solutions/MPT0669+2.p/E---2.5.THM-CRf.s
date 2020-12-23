%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0669+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:50 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 274 expanded)
%              Number of clauses        :   34 ( 107 expanded)
%              Number of leaves         :   11 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  299 (1257 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(t117_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k8_relat_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t117_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',dt_k8_relat_1)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(fc9_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k8_relat_1(X1,X2))
        & v1_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t25_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(t115_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t115_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t85_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( X2 = k8_relat_1(X1,X3)
          <=> ( ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(X4,k1_relat_1(X3))
                    & r2_hidden(k1_funct_1(X3,X4),X1) ) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
        <=> ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_funct_1])).

fof(c_0_12,plain,(
    ! [X2325,X2326] :
      ( ~ v1_relat_1(X2326)
      | r1_tarski(k8_relat_1(X2325,X2326),X2326) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk200_0)
    & v1_funct_1(esk200_0)
    & ( ~ r2_hidden(esk198_0,k1_relat_1(k8_relat_1(esk199_0,esk200_0)))
      | ~ r2_hidden(esk198_0,k1_relat_1(esk200_0))
      | ~ r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0) )
    & ( r2_hidden(esk198_0,k1_relat_1(esk200_0))
      | r2_hidden(esk198_0,k1_relat_1(k8_relat_1(esk199_0,esk200_0))) )
    & ( r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0)
      | r2_hidden(esk198_0,k1_relat_1(k8_relat_1(esk199_0,esk200_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X2229,X2230] :
      ( ~ v1_relat_1(X2230)
      | v1_relat_1(k8_relat_1(X2229,X2230)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_15,plain,(
    ! [X2719,X2720,X2721] :
      ( ( X2721 != k1_funct_1(X2719,X2720)
        | r2_hidden(k4_tarski(X2720,X2721),X2719)
        | ~ r2_hidden(X2720,k1_relat_1(X2719))
        | ~ v1_relat_1(X2719)
        | ~ v1_funct_1(X2719) )
      & ( ~ r2_hidden(k4_tarski(X2720,X2721),X2719)
        | X2721 = k1_funct_1(X2719,X2720)
        | ~ r2_hidden(X2720,k1_relat_1(X2719))
        | ~ v1_relat_1(X2719)
        | ~ v1_funct_1(X2719) )
      & ( X2721 != k1_funct_1(X2719,X2720)
        | X2721 = k1_xboole_0
        | r2_hidden(X2720,k1_relat_1(X2719))
        | ~ v1_relat_1(X2719)
        | ~ v1_funct_1(X2719) )
      & ( X2721 != k1_xboole_0
        | X2721 = k1_funct_1(X2719,X2720)
        | r2_hidden(X2720,k1_relat_1(X2719))
        | ~ v1_relat_1(X2719)
        | ~ v1_funct_1(X2719) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_16,plain,(
    ! [X2759,X2760] :
      ( ( v1_relat_1(k8_relat_1(X2759,X2760))
        | ~ v1_relat_1(X2760)
        | ~ v1_funct_1(X2760) )
      & ( v1_funct_1(k8_relat_1(X2759,X2760))
        | ~ v1_relat_1(X2760)
        | ~ v1_funct_1(X2760) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).

fof(c_0_17,plain,(
    ! [X2595,X2596] :
      ( ( r1_tarski(k1_relat_1(X2595),k1_relat_1(X2596))
        | ~ r1_tarski(X2595,X2596)
        | ~ v1_relat_1(X2596)
        | ~ v1_relat_1(X2595) )
      & ( r1_tarski(k2_relat_1(X2595),k2_relat_1(X2596))
        | ~ r1_tarski(X2595,X2596)
        | ~ v1_relat_1(X2596)
        | ~ v1_relat_1(X2595) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(k8_relat_1(X2,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk200_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk200_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk200_0),esk200_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk200_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

fof(c_0_28,plain,(
    ! [X2799,X2800] :
      ( ~ v1_relat_1(X2800)
      | ~ v1_funct_1(X2800)
      | ~ r2_hidden(X2799,k1_relat_1(X2800))
      | r2_hidden(k1_funct_1(X2800,X2799),k2_relat_1(X2800)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0)
    | r2_hidden(esk198_0,k1_relat_1(k8_relat_1(esk199_0,esk200_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(k8_relat_1(X1,esk200_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,esk200_0)),k1_relat_1(esk200_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_19]),c_0_27])])).

fof(c_0_34,plain,(
    ! [X2320,X2321,X2322] :
      ( ( r2_hidden(X2320,X2321)
        | ~ r2_hidden(X2320,k2_relat_1(k8_relat_1(X2321,X2322)))
        | ~ v1_relat_1(X2322) )
      & ( r2_hidden(X2320,k2_relat_1(X2322))
        | ~ r2_hidden(X2320,k2_relat_1(k8_relat_1(X2321,X2322)))
        | ~ v1_relat_1(X2322) )
      & ( ~ r2_hidden(X2320,X2321)
        | ~ r2_hidden(X2320,k2_relat_1(X2322))
        | r2_hidden(X2320,k2_relat_1(k8_relat_1(X2321,X2322)))
        | ~ v1_relat_1(X2322) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t115_relat_1])])])).

cnf(c_0_35,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X2942,X2943,X2944] :
      ( ( r2_hidden(X2942,k1_relat_1(X2944))
        | ~ r2_hidden(k4_tarski(X2942,X2943),X2944)
        | ~ v1_relat_1(X2944)
        | ~ v1_funct_1(X2944) )
      & ( X2943 = k1_funct_1(X2944,X2942)
        | ~ r2_hidden(k4_tarski(X2942,X2943),X2944)
        | ~ v1_relat_1(X2944)
        | ~ v1_funct_1(X2944) )
      & ( ~ r2_hidden(X2942,k1_relat_1(X2944))
        | X2943 != k1_funct_1(X2944,X2942)
        | r2_hidden(k4_tarski(X2942,X2943),X2944)
        | ~ v1_relat_1(X2944)
        | ~ v1_funct_1(X2944) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk200_0)
    | ~ r2_hidden(X1,k8_relat_1(X2,esk200_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk198_0,k1_funct_1(k8_relat_1(esk199_0,esk200_0),esk198_0)),k8_relat_1(esk199_0,esk200_0))
    | r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_27])])).

fof(c_0_39,plain,(
    ! [X2931,X2932,X2933,X2934,X2935,X2936] :
      ( ( r2_hidden(X2934,k1_relat_1(X2933))
        | ~ r2_hidden(X2934,k1_relat_1(X2932))
        | X2932 != k8_relat_1(X2931,X2933)
        | ~ v1_relat_1(X2933)
        | ~ v1_funct_1(X2933)
        | ~ v1_relat_1(X2932)
        | ~ v1_funct_1(X2932) )
      & ( r2_hidden(k1_funct_1(X2933,X2934),X2931)
        | ~ r2_hidden(X2934,k1_relat_1(X2932))
        | X2932 != k8_relat_1(X2931,X2933)
        | ~ v1_relat_1(X2933)
        | ~ v1_funct_1(X2933)
        | ~ v1_relat_1(X2932)
        | ~ v1_funct_1(X2932) )
      & ( ~ r2_hidden(X2935,k1_relat_1(X2933))
        | ~ r2_hidden(k1_funct_1(X2933,X2935),X2931)
        | r2_hidden(X2935,k1_relat_1(X2932))
        | X2932 != k8_relat_1(X2931,X2933)
        | ~ v1_relat_1(X2933)
        | ~ v1_funct_1(X2933)
        | ~ v1_relat_1(X2932)
        | ~ v1_funct_1(X2932) )
      & ( ~ r2_hidden(X2936,k1_relat_1(X2932))
        | k1_funct_1(X2932,X2936) = k1_funct_1(X2933,X2936)
        | X2932 != k8_relat_1(X2931,X2933)
        | ~ v1_relat_1(X2933)
        | ~ v1_funct_1(X2933)
        | ~ v1_relat_1(X2932)
        | ~ v1_funct_1(X2932) )
      & ( r2_hidden(esk197_3(X2931,X2932,X2933),k1_relat_1(X2932))
        | ~ r2_hidden(esk196_3(X2931,X2932,X2933),k1_relat_1(X2932))
        | ~ r2_hidden(esk196_3(X2931,X2932,X2933),k1_relat_1(X2933))
        | ~ r2_hidden(k1_funct_1(X2933,esk196_3(X2931,X2932,X2933)),X2931)
        | X2932 = k8_relat_1(X2931,X2933)
        | ~ v1_relat_1(X2933)
        | ~ v1_funct_1(X2933)
        | ~ v1_relat_1(X2932)
        | ~ v1_funct_1(X2932) )
      & ( k1_funct_1(X2932,esk197_3(X2931,X2932,X2933)) != k1_funct_1(X2933,esk197_3(X2931,X2932,X2933))
        | ~ r2_hidden(esk196_3(X2931,X2932,X2933),k1_relat_1(X2932))
        | ~ r2_hidden(esk196_3(X2931,X2932,X2933),k1_relat_1(X2933))
        | ~ r2_hidden(k1_funct_1(X2933,esk196_3(X2931,X2932,X2933)),X2931)
        | X2932 = k8_relat_1(X2931,X2933)
        | ~ v1_relat_1(X2933)
        | ~ v1_funct_1(X2933)
        | ~ v1_relat_1(X2932)
        | ~ v1_funct_1(X2932) )
      & ( r2_hidden(esk197_3(X2931,X2932,X2933),k1_relat_1(X2932))
        | r2_hidden(esk196_3(X2931,X2932,X2933),k1_relat_1(X2933))
        | r2_hidden(esk196_3(X2931,X2932,X2933),k1_relat_1(X2932))
        | X2932 = k8_relat_1(X2931,X2933)
        | ~ v1_relat_1(X2933)
        | ~ v1_funct_1(X2933)
        | ~ v1_relat_1(X2932)
        | ~ v1_funct_1(X2932) )
      & ( k1_funct_1(X2932,esk197_3(X2931,X2932,X2933)) != k1_funct_1(X2933,esk197_3(X2931,X2932,X2933))
        | r2_hidden(esk196_3(X2931,X2932,X2933),k1_relat_1(X2933))
        | r2_hidden(esk196_3(X2931,X2932,X2933),k1_relat_1(X2932))
        | X2932 = k8_relat_1(X2931,X2933)
        | ~ v1_relat_1(X2933)
        | ~ v1_funct_1(X2933)
        | ~ v1_relat_1(X2932)
        | ~ v1_funct_1(X2932) )
      & ( r2_hidden(esk197_3(X2931,X2932,X2933),k1_relat_1(X2932))
        | r2_hidden(k1_funct_1(X2933,esk196_3(X2931,X2932,X2933)),X2931)
        | r2_hidden(esk196_3(X2931,X2932,X2933),k1_relat_1(X2932))
        | X2932 = k8_relat_1(X2931,X2933)
        | ~ v1_relat_1(X2933)
        | ~ v1_funct_1(X2933)
        | ~ v1_relat_1(X2932)
        | ~ v1_funct_1(X2932) )
      & ( k1_funct_1(X2932,esk197_3(X2931,X2932,X2933)) != k1_funct_1(X2933,esk197_3(X2931,X2932,X2933))
        | r2_hidden(k1_funct_1(X2933,esk196_3(X2931,X2932,X2933)),X2931)
        | r2_hidden(esk196_3(X2931,X2932,X2933),k1_relat_1(X2932))
        | X2932 = k8_relat_1(X2931,X2933)
        | ~ v1_relat_1(X2933)
        | ~ v1_funct_1(X2933)
        | ~ v1_relat_1(X2932)
        | ~ v1_funct_1(X2932) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk200_0))
    | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X2,esk200_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk198_0,k1_relat_1(esk200_0))
    | r2_hidden(esk198_0,k1_relat_1(k8_relat_1(esk199_0,esk200_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k1_funct_1(k8_relat_1(esk199_0,esk200_0),esk198_0),k2_relat_1(k8_relat_1(esk199_0,esk200_0)))
    | r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_32]),c_0_27])])).

cnf(c_0_44,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk198_0,k1_funct_1(k8_relat_1(esk199_0,esk200_0),esk198_0)),esk200_0)
    | r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_relat_1(X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | X4 != k8_relat_1(X3,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk198_0,k1_relat_1(k8_relat_1(esk199_0,esk200_0)))
    | ~ r2_hidden(esk198_0,k1_relat_1(esk200_0))
    | ~ r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk198_0,k1_relat_1(esk200_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k1_funct_1(k8_relat_1(esk199_0,esk200_0),esk198_0),esk199_0)
    | r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_19])])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk199_0,esk200_0),esk198_0) = k1_funct_1(esk200_0,esk198_0)
    | r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_24]),c_0_19])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k1_funct_1(X3,X1),X2)
    | ~ r2_hidden(X1,k1_relat_1(X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_20]),c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk198_0,k1_relat_1(k8_relat_1(esk199_0,esk200_0)))
    | ~ r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk200_0,esk198_0),esk199_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk198_0,k1_relat_1(k8_relat_1(X1,esk200_0)))
    | ~ r2_hidden(k1_funct_1(esk200_0,esk198_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_24]),c_0_19])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk198_0,k1_relat_1(k8_relat_1(esk199_0,esk200_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
