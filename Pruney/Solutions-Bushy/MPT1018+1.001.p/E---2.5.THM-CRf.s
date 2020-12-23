%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1018+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:35 EST 2020

% Result     : Theorem 0.09s
% Output     : CNFRefutation 0.09s
% Verified   : 
% Statistics : Number of formulae       :   17 (  38 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    2 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 252 expanded)
%              Number of equality atoms :   20 (  62 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t85_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
       => ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(t77_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
         => ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t85_funct_2])).

fof(c_0_3,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ v2_funct_1(X6)
        | ~ r2_hidden(X7,X5)
        | ~ r2_hidden(X8,X5)
        | k1_funct_1(X6,X7) != k1_funct_1(X6,X8)
        | X7 = X8
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,X5,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | v2_funct_1(X6)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,X5,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) )
      & ( r2_hidden(esk2_2(X5,X6),X5)
        | v2_funct_1(X6)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,X5,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) )
      & ( k1_funct_1(X6,esk1_2(X5,X6)) = k1_funct_1(X6,esk2_2(X5,X6))
        | v2_funct_1(X6)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,X5,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) )
      & ( esk1_2(X5,X6) != esk2_2(X5,X6)
        | v2_funct_1(X6)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,X5,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_funct_2])])])])])).

fof(c_0_4,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk3_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    & v2_funct_1(esk4_0)
    & r2_hidden(esk5_0,esk3_0)
    & r2_hidden(esk6_0,esk3_0)
    & k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( X2 = X4
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X3)
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8]),c_0_9])])).

cnf(c_0_11,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( X1 = esk6_0
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])]),c_0_15]),
    [proof]).

%------------------------------------------------------------------------------
