%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 206 expanded)
%              Number of clauses        :   46 (  79 expanded)
%              Number of leaves         :   10 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  269 (1267 expanded)
%              Number of equality atoms :   70 ( 170 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t191_funct_2,conjecture,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ~ v1_xboole_0(X3)
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
             => ( ! [X5] :
                    ( m1_subset_1(X5,X2)
                   => r2_hidden(k3_funct_2(X2,X3,X4,X5),X1) )
               => r1_tarski(k2_relset_1(X2,X3,X4),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t5_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k1_relat_1(X3) = X1
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => r2_hidden(k1_funct_1(X3,X4),X2) ) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(t11_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ~ v1_xboole_0(X3)
           => ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
               => ( ! [X5] :
                      ( m1_subset_1(X5,X2)
                     => r2_hidden(k3_funct_2(X2,X3,X4,X5),X1) )
                 => r1_tarski(k2_relset_1(X2,X3,X4),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t191_funct_2])).

fof(c_0_11,negated_conjecture,(
    ! [X53] :
      ( ~ v1_xboole_0(esk8_0)
      & ~ v1_xboole_0(esk9_0)
      & v1_funct_1(esk10_0)
      & v1_funct_2(esk10_0,esk8_0,esk9_0)
      & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))
      & ( ~ m1_subset_1(X53,esk8_0)
        | r2_hidden(k3_funct_2(esk8_0,esk9_0,esk10_0,X53),esk7_0) )
      & ~ r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),esk7_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_12,plain,(
    ! [X33,X34,X35,X36] :
      ( v1_xboole_0(X33)
      | ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,X33,X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | ~ m1_subset_1(X36,X33)
      | k3_funct_2(X33,X34,X35,X36) = k1_funct_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_13,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | v1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_14,plain,(
    ! [X45,X46,X47] :
      ( ( v1_funct_1(X47)
        | r2_hidden(esk6_3(X45,X46,X47),X45)
        | k1_relat_1(X47) != X45
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( v1_funct_2(X47,X45,X46)
        | r2_hidden(esk6_3(X45,X46,X47),X45)
        | k1_relat_1(X47) != X45
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | r2_hidden(esk6_3(X45,X46,X47),X45)
        | k1_relat_1(X47) != X45
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( v1_funct_1(X47)
        | ~ r2_hidden(k1_funct_1(X47,esk6_3(X45,X46,X47)),X46)
        | k1_relat_1(X47) != X45
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( v1_funct_2(X47,X45,X46)
        | ~ r2_hidden(k1_funct_1(X47,esk6_3(X45,X46,X47)),X46)
        | k1_relat_1(X47) != X45
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ r2_hidden(k1_funct_1(X47,esk6_3(X45,X46,X47)),X46)
        | k1_relat_1(X47) != X45
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk8_0,esk9_0,esk10_0,X1),esk7_0)
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk10_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(k1_funct_1(X1,esk6_3(X2,X3,X1)),X3)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk10_0,X1),esk7_0)
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

fof(c_0_25,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | m1_subset_1(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_26,plain,(
    ! [X20,X21,X22,X23,X25,X26,X27,X28,X29,X31] :
      ( ( v1_relat_1(esk2_4(X20,X21,X22,X23))
        | ~ r2_hidden(X23,X22)
        | X22 != k1_funct_2(X20,X21) )
      & ( v1_funct_1(esk2_4(X20,X21,X22,X23))
        | ~ r2_hidden(X23,X22)
        | X22 != k1_funct_2(X20,X21) )
      & ( X23 = esk2_4(X20,X21,X22,X23)
        | ~ r2_hidden(X23,X22)
        | X22 != k1_funct_2(X20,X21) )
      & ( k1_relat_1(esk2_4(X20,X21,X22,X23)) = X20
        | ~ r2_hidden(X23,X22)
        | X22 != k1_funct_2(X20,X21) )
      & ( r1_tarski(k2_relat_1(esk2_4(X20,X21,X22,X23)),X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k1_funct_2(X20,X21) )
      & ( ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | X25 != X26
        | k1_relat_1(X26) != X20
        | ~ r1_tarski(k2_relat_1(X26),X21)
        | r2_hidden(X25,X22)
        | X22 != k1_funct_2(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X27,X28,X29),X29)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31)
        | esk3_3(X27,X28,X29) != X31
        | k1_relat_1(X31) != X27
        | ~ r1_tarski(k2_relat_1(X31),X28)
        | X29 = k1_funct_2(X27,X28) )
      & ( v1_relat_1(esk4_3(X27,X28,X29))
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k1_funct_2(X27,X28) )
      & ( v1_funct_1(esk4_3(X27,X28,X29))
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k1_funct_2(X27,X28) )
      & ( esk3_3(X27,X28,X29) = esk4_3(X27,X28,X29)
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k1_funct_2(X27,X28) )
      & ( k1_relat_1(esk4_3(X27,X28,X29)) = X27
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k1_funct_2(X27,X28) )
      & ( r1_tarski(k2_relat_1(esk4_3(X27,X28,X29)),X28)
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k1_funct_2(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk10_0,X1,esk7_0)
    | k1_relat_1(esk10_0) != X1
    | ~ m1_subset_1(esk6_3(X1,esk7_0,esk10_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_18]),c_0_24])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(k1_funct_1(X1,esk6_3(X2,X3,X1)),X3)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( k1_relat_1(esk2_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( X1 = esk2_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X37,X38,X39] :
      ( ( X38 = k1_xboole_0
        | r2_hidden(X39,k1_funct_2(X37,X38))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_xboole_0
        | r2_hidden(X39,k1_funct_2(X37,X38))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk10_0,X1,esk7_0)
    | k1_relat_1(esk10_0) != X1
    | ~ r2_hidden(esk6_3(X1,esk7_0,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk6_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))
    | k1_relat_1(esk10_0) != X1
    | ~ m1_subset_1(esk6_3(X1,esk7_0,esk10_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_18]),c_0_24])])).

cnf(c_0_36,plain,
    ( k1_relat_1(X1) = X2
    | X3 != k1_funct_2(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk10_0,esk8_0,esk7_0)
    | k1_relat_1(esk10_0) != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_18]),c_0_24])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))
    | k1_relat_1(esk10_0) != X1
    | ~ r2_hidden(esk6_3(X1,esk7_0,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(esk6_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(esk10_0,k1_funct_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_relat_1(esk2_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk10_0,k1_funct_2(esk8_0,esk7_0))
    | k1_relat_1(esk10_0) != esk8_0
    | ~ m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_18])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))
    | k1_relat_1(esk10_0) != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_18]),c_0_24])])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(esk10_0) = esk8_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_49,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | k2_relset_1(X17,X18,X19) = k2_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_50,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | X3 != k1_funct_2(X4,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk10_0,k1_funct_2(esk8_0,esk7_0))
    | k1_relat_1(esk10_0) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk10_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk10_0,k1_funct_2(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk10_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_19])])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(X1,esk8_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_15])).

cnf(c_0_61,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_subset_1(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_48])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_28])).

cnf(c_0_64,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t191_funct_2, conjecture, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 0.20/0.39  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.20/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.39  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 0.20/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.39  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 0.20/0.39  fof(t11_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_funct_2)).
% 0.20/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.39  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1)))))), inference(assume_negation,[status(cth)],[t191_funct_2])).
% 0.20/0.39  fof(c_0_11, negated_conjecture, ![X53]:(~v1_xboole_0(esk8_0)&(~v1_xboole_0(esk9_0)&(((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk8_0,esk9_0))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0))))&((~m1_subset_1(X53,esk8_0)|r2_hidden(k3_funct_2(esk8_0,esk9_0,esk10_0,X53),esk7_0))&~r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),esk7_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 0.20/0.39  fof(c_0_12, plain, ![X33, X34, X35, X36]:(v1_xboole_0(X33)|~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|~m1_subset_1(X36,X33)|k3_funct_2(X33,X34,X35,X36)=k1_funct_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.20/0.39  fof(c_0_13, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|v1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.39  fof(c_0_14, plain, ![X45, X46, X47]:((((v1_funct_1(X47)|(r2_hidden(esk6_3(X45,X46,X47),X45)|k1_relat_1(X47)!=X45)|(~v1_relat_1(X47)|~v1_funct_1(X47)))&(v1_funct_2(X47,X45,X46)|(r2_hidden(esk6_3(X45,X46,X47),X45)|k1_relat_1(X47)!=X45)|(~v1_relat_1(X47)|~v1_funct_1(X47))))&(m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|(r2_hidden(esk6_3(X45,X46,X47),X45)|k1_relat_1(X47)!=X45)|(~v1_relat_1(X47)|~v1_funct_1(X47))))&(((v1_funct_1(X47)|(~r2_hidden(k1_funct_1(X47,esk6_3(X45,X46,X47)),X46)|k1_relat_1(X47)!=X45)|(~v1_relat_1(X47)|~v1_funct_1(X47)))&(v1_funct_2(X47,X45,X46)|(~r2_hidden(k1_funct_1(X47,esk6_3(X45,X46,X47)),X46)|k1_relat_1(X47)!=X45)|(~v1_relat_1(X47)|~v1_funct_1(X47))))&(m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|(~r2_hidden(k1_funct_1(X47,esk6_3(X45,X46,X47)),X46)|k1_relat_1(X47)!=X45)|(~v1_relat_1(X47)|~v1_funct_1(X47))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (r2_hidden(k3_funct_2(esk8_0,esk9_0,esk10_0,X1),esk7_0)|~m1_subset_1(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_16, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk10_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_21, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_22, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(k1_funct_1(X1,esk6_3(X2,X3,X1)),X3)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (r2_hidden(k1_funct_1(esk10_0,X1),esk7_0)|~m1_subset_1(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.20/0.39  fof(c_0_25, plain, ![X12, X13]:(~r2_hidden(X12,X13)|m1_subset_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.39  fof(c_0_26, plain, ![X20, X21, X22, X23, X25, X26, X27, X28, X29, X31]:(((((((v1_relat_1(esk2_4(X20,X21,X22,X23))|~r2_hidden(X23,X22)|X22!=k1_funct_2(X20,X21))&(v1_funct_1(esk2_4(X20,X21,X22,X23))|~r2_hidden(X23,X22)|X22!=k1_funct_2(X20,X21)))&(X23=esk2_4(X20,X21,X22,X23)|~r2_hidden(X23,X22)|X22!=k1_funct_2(X20,X21)))&(k1_relat_1(esk2_4(X20,X21,X22,X23))=X20|~r2_hidden(X23,X22)|X22!=k1_funct_2(X20,X21)))&(r1_tarski(k2_relat_1(esk2_4(X20,X21,X22,X23)),X21)|~r2_hidden(X23,X22)|X22!=k1_funct_2(X20,X21)))&(~v1_relat_1(X26)|~v1_funct_1(X26)|X25!=X26|k1_relat_1(X26)!=X20|~r1_tarski(k2_relat_1(X26),X21)|r2_hidden(X25,X22)|X22!=k1_funct_2(X20,X21)))&((~r2_hidden(esk3_3(X27,X28,X29),X29)|(~v1_relat_1(X31)|~v1_funct_1(X31)|esk3_3(X27,X28,X29)!=X31|k1_relat_1(X31)!=X27|~r1_tarski(k2_relat_1(X31),X28))|X29=k1_funct_2(X27,X28))&(((((v1_relat_1(esk4_3(X27,X28,X29))|r2_hidden(esk3_3(X27,X28,X29),X29)|X29=k1_funct_2(X27,X28))&(v1_funct_1(esk4_3(X27,X28,X29))|r2_hidden(esk3_3(X27,X28,X29),X29)|X29=k1_funct_2(X27,X28)))&(esk3_3(X27,X28,X29)=esk4_3(X27,X28,X29)|r2_hidden(esk3_3(X27,X28,X29),X29)|X29=k1_funct_2(X27,X28)))&(k1_relat_1(esk4_3(X27,X28,X29))=X27|r2_hidden(esk3_3(X27,X28,X29),X29)|X29=k1_funct_2(X27,X28)))&(r1_tarski(k2_relat_1(esk4_3(X27,X28,X29)),X28)|r2_hidden(esk3_3(X27,X28,X29),X29)|X29=k1_funct_2(X27,X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk10_0,X1,esk7_0)|k1_relat_1(esk10_0)!=X1|~m1_subset_1(esk6_3(X1,esk7_0,esk10_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_18]), c_0_24])])).
% 0.20/0.39  cnf(c_0_28, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(k1_funct_1(X1,esk6_3(X2,X3,X1)),X3)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_30, plain, (k1_relat_1(esk2_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_31, plain, (X1=esk2_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  fof(c_0_32, plain, ![X37, X38, X39]:((X38=k1_xboole_0|r2_hidden(X39,k1_funct_2(X37,X38))|(~v1_funct_1(X39)|~v1_funct_2(X39,X37,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&(X37!=k1_xboole_0|r2_hidden(X39,k1_funct_2(X37,X38))|(~v1_funct_1(X39)|~v1_funct_2(X39,X37,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk10_0,X1,esk7_0)|k1_relat_1(esk10_0)!=X1|~r2_hidden(esk6_3(X1,esk7_0,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.39  cnf(c_0_34, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk6_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))|k1_relat_1(esk10_0)!=X1|~m1_subset_1(esk6_3(X1,esk7_0,esk10_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_23]), c_0_18]), c_0_24])])).
% 0.20/0.39  cnf(c_0_36, plain, (k1_relat_1(X1)=X2|X3!=k1_funct_2(X2,X4)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.39  cnf(c_0_37, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_funct_2(X3,X1))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk10_0,esk8_0,esk7_0)|k1_relat_1(esk10_0)!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_18]), c_0_24])])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))|k1_relat_1(esk10_0)!=X1|~r2_hidden(esk6_3(X1,esk7_0,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_35, c_0_28])).
% 0.20/0.39  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|r2_hidden(esk6_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_41, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(esk10_0,k1_funct_2(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.39  cnf(c_0_43, plain, (r1_tarski(k2_relat_1(esk2_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk10_0,k1_funct_2(esk8_0,esk7_0))|k1_relat_1(esk10_0)!=esk8_0|~m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_18])])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))|k1_relat_1(esk10_0)!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_18]), c_0_24])])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (k1_relat_1(esk10_0)=esk8_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.39  cnf(c_0_48, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.39  fof(c_0_49, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|k2_relset_1(X17,X18,X19)=k2_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.39  fof(c_0_50, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.39  cnf(c_0_51, plain, (r1_tarski(k2_relat_1(X1),X2)|X3!=k1_funct_2(X4,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_43, c_0_31])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk10_0,k1_funct_2(esk8_0,esk7_0))|k1_relat_1(esk10_0)!=esk8_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (k1_relat_1(esk10_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (~r1_tarski(k2_relset_1(esk8_0,esk9_0,esk10_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_55, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.39  cnf(c_0_56, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_57, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(er,[status(thm)],[c_0_51])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk10_0,k1_funct_2(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (~r1_tarski(k2_relat_1(esk10_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_19])])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (~m1_subset_1(X1,esk8_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_15])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (~m1_subset_1(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_48])])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_62, c_0_28])).
% 0.20/0.39  cnf(c_0_64, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_20]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 66
% 0.20/0.39  # Proof object clause steps            : 46
% 0.20/0.39  # Proof object formula steps           : 20
% 0.20/0.39  # Proof object conjectures             : 30
% 0.20/0.39  # Proof object clause conjectures      : 27
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 22
% 0.20/0.39  # Proof object initial formulas used   : 10
% 0.20/0.39  # Proof object generating inferences   : 22
% 0.20/0.39  # Proof object simplifying inferences  : 33
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 12
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 39
% 0.20/0.39  # Removed in clause preprocessing      : 2
% 0.20/0.39  # Initial clauses in saturation        : 37
% 0.20/0.39  # Processed clauses                    : 152
% 0.20/0.39  # ...of these trivial                  : 1
% 0.20/0.39  # ...subsumed                          : 12
% 0.20/0.39  # ...remaining for further processing  : 139
% 0.20/0.39  # Other redundant clauses eliminated   : 6
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 5
% 0.20/0.39  # Backward-rewritten                   : 27
% 0.20/0.39  # Generated clauses                    : 167
% 0.20/0.39  # ...of the previous two non-trivial   : 160
% 0.20/0.39  # Contextual simplify-reflections      : 3
% 0.20/0.39  # Paramodulations                      : 154
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 13
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 68
% 0.20/0.39  #    Positive orientable unit clauses  : 8
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 5
% 0.20/0.39  #    Non-unit-clauses                  : 55
% 0.20/0.39  # Current number of unprocessed clauses: 70
% 0.20/0.39  # ...number of literals in the above   : 310
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 68
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1234
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 389
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 16
% 0.20/0.39  # Unit Clause-clause subsumption calls : 94
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 11
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 5755
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.037 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.042 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
