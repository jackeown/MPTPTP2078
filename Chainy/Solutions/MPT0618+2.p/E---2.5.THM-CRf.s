%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0618+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:49 EST 2020

% Result     : Theorem 1.03s
% Output     : CNFRefutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   13 (  22 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    2 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   67 ( 103 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t12_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(c_0_2,plain,(
    ! [X2721,X2722,X2723,X2725,X2726,X2727,X2729] :
      ( ( r2_hidden(esk158_3(X2721,X2722,X2723),k1_relat_1(X2721))
        | ~ r2_hidden(X2723,X2722)
        | X2722 != k2_relat_1(X2721)
        | ~ v1_relat_1(X2721)
        | ~ v1_funct_1(X2721) )
      & ( X2723 = k1_funct_1(X2721,esk158_3(X2721,X2722,X2723))
        | ~ r2_hidden(X2723,X2722)
        | X2722 != k2_relat_1(X2721)
        | ~ v1_relat_1(X2721)
        | ~ v1_funct_1(X2721) )
      & ( ~ r2_hidden(X2726,k1_relat_1(X2721))
        | X2725 != k1_funct_1(X2721,X2726)
        | r2_hidden(X2725,X2722)
        | X2722 != k2_relat_1(X2721)
        | ~ v1_relat_1(X2721)
        | ~ v1_funct_1(X2721) )
      & ( ~ r2_hidden(esk159_2(X2721,X2727),X2727)
        | ~ r2_hidden(X2729,k1_relat_1(X2721))
        | esk159_2(X2721,X2727) != k1_funct_1(X2721,X2729)
        | X2727 = k2_relat_1(X2721)
        | ~ v1_relat_1(X2721)
        | ~ v1_funct_1(X2721) )
      & ( r2_hidden(esk160_2(X2721,X2727),k1_relat_1(X2721))
        | r2_hidden(esk159_2(X2721,X2727),X2727)
        | X2727 = k2_relat_1(X2721)
        | ~ v1_relat_1(X2721)
        | ~ v1_funct_1(X2721) )
      & ( esk159_2(X2721,X2727) = k1_funct_1(X2721,esk160_2(X2721,X2727))
        | r2_hidden(esk159_2(X2721,X2727),X2727)
        | X2727 = k2_relat_1(X2721)
        | ~ v1_relat_1(X2721)
        | ~ v1_funct_1(X2721) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t12_funct_1])).

cnf(c_0_4,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk163_0)
    & v1_funct_1(esk163_0)
    & r2_hidden(esk162_0,k1_relat_1(esk163_0))
    & ~ r2_hidden(k1_funct_1(esk163_0,esk162_0),k2_relat_1(esk163_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_4])])).

cnf(c_0_7,negated_conjecture,
    ( v1_funct_1(esk163_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk163_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk163_0,esk162_0),k2_relat_1(esk163_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk163_0,X1),k2_relat_1(esk163_0))
    | ~ r2_hidden(X1,k1_relat_1(esk163_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk162_0,k1_relat_1(esk163_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
