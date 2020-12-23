%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:57 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 (3053 expanded)
%              Number of clauses        :   74 (1094 expanded)
%              Number of leaves         :   15 ( 771 expanded)
%              Depth                    :   17
%              Number of atoms          :  478 (31249 expanded)
%              Number of equality atoms :  151 (12563 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( ( k2_relset_1(X1,X2,X3) = X2
              & v2_funct_1(X3)
              & ! [X5,X6] :
                  ( ( ( r2_hidden(X5,X2)
                      & k1_funct_1(X4,X5) = X6 )
                   => ( r2_hidden(X6,X1)
                      & k1_funct_1(X3,X6) = X5 ) )
                  & ( ( r2_hidden(X6,X1)
                      & k1_funct_1(X3,X6) = X5 )
                   => ( r2_hidden(X5,X2)
                      & k1_funct_1(X4,X5) = X6 ) ) ) )
           => ( X1 = k1_xboole_0
              | X2 = k1_xboole_0
              | X4 = k2_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_2)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t60_funct_1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( ( k2_relset_1(X1,X2,X3) = X2
                & v2_funct_1(X3)
                & ! [X5,X6] :
                    ( ( ( r2_hidden(X5,X2)
                        & k1_funct_1(X4,X5) = X6 )
                     => ( r2_hidden(X6,X1)
                        & k1_funct_1(X3,X6) = X5 ) )
                    & ( ( r2_hidden(X6,X1)
                        & k1_funct_1(X3,X6) = X5 )
                     => ( r2_hidden(X5,X2)
                        & k1_funct_1(X4,X5) = X6 ) ) ) )
             => ( X1 = k1_xboole_0
                | X2 = k1_xboole_0
                | X4 = k2_funct_1(X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_funct_2])).

fof(c_0_16,plain,(
    ! [X32,X33,X34] :
      ( ( ~ v1_funct_2(X34,X32,X33)
        | X32 = k1_relset_1(X32,X33,X34)
        | X33 = k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X32 != k1_relset_1(X32,X33,X34)
        | v1_funct_2(X34,X32,X33)
        | X33 = k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ v1_funct_2(X34,X32,X33)
        | X32 = k1_relset_1(X32,X33,X34)
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X32 != k1_relset_1(X32,X33,X34)
        | v1_funct_2(X34,X32,X33)
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ v1_funct_2(X34,X32,X33)
        | X34 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X34 != k1_xboole_0
        | v1_funct_2(X34,X32,X33)
        | X32 = k1_xboole_0
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_17,negated_conjecture,(
    ! [X47,X48] :
      ( v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,esk4_0,esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk5_0,esk4_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))
      & k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0
      & v2_funct_1(esk6_0)
      & ( r2_hidden(X48,esk4_0)
        | ~ r2_hidden(X47,esk5_0)
        | k1_funct_1(esk7_0,X47) != X48 )
      & ( k1_funct_1(esk6_0,X48) = X47
        | ~ r2_hidden(X47,esk5_0)
        | k1_funct_1(esk7_0,X47) != X48 )
      & ( r2_hidden(X47,esk5_0)
        | ~ r2_hidden(X48,esk4_0)
        | k1_funct_1(esk6_0,X48) != X47 )
      & ( k1_funct_1(esk7_0,X47) = X48
        | ~ r2_hidden(X48,esk4_0)
        | k1_funct_1(esk6_0,X48) != X47 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk7_0 != k2_funct_1(esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_19,plain,(
    ! [X13,X14] : v1_relat_1(k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_20,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k1_relset_1(X26,X27,X28) = k1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_21,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X39,X40,X41] :
      ( ( v1_funct_1(X41)
        | r2_hidden(esk3_3(X39,X40,X41),X39)
        | k1_relat_1(X41) != X39
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41) )
      & ( v1_funct_2(X41,X39,X40)
        | r2_hidden(esk3_3(X39,X40,X41),X39)
        | k1_relat_1(X41) != X39
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41) )
      & ( m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | r2_hidden(esk3_3(X39,X40,X41),X39)
        | k1_relat_1(X41) != X39
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41) )
      & ( v1_funct_1(X41)
        | ~ r2_hidden(k1_funct_1(X41,esk3_3(X39,X40,X41)),X40)
        | k1_relat_1(X41) != X39
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41) )
      & ( v1_funct_2(X41,X39,X40)
        | ~ r2_hidden(k1_funct_1(X41,esk3_3(X39,X40,X41)),X40)
        | k1_relat_1(X41) != X39
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41) )
      & ( m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ r2_hidden(k1_funct_1(X41,esk3_3(X39,X40,X41)),X40)
        | k1_relat_1(X41) != X39
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | ~ r2_hidden(X16,k1_relat_1(X17))
      | r2_hidden(k1_funct_1(X17,X16),k2_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = X2
    | ~ r2_hidden(X2,esk4_0)
    | k1_funct_1(esk6_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(esk5_0,esk4_0,esk7_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk4_0)
    | k1_funct_1(esk6_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_33,plain,(
    ! [X35,X36,X37] :
      ( ( v1_funct_1(k2_funct_1(X37))
        | ~ v2_funct_1(X37)
        | k2_relset_1(X35,X36,X37) != X36
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( v1_funct_2(k2_funct_1(X37),X36,X35)
        | ~ v2_funct_1(X37)
        | k2_relset_1(X35,X36,X37) != X36
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( m1_subset_1(k2_funct_1(X37),k1_zfmisc_1(k2_zfmisc_1(X36,X35)))
        | ~ v2_funct_1(X37)
        | k2_relset_1(X35,X36,X37) != X36
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(k1_funct_1(X1,esk3_3(X2,X3,X1)),X3)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1)) = X1
    | ~ r2_hidden(X1,esk4_0) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_29])])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_22])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X18] :
      ( ( k2_relat_1(X18) = k1_relat_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k1_relat_1(X18) = k2_relat_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_42,plain,(
    ! [X15] :
      ( ( v1_relat_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( v1_funct_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(esk3_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_47,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r2_hidden(k1_funct_1(X1,esk3_3(k1_relat_1(X1),X2,X1)),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])]),c_0_39]),c_0_40])).

cnf(c_0_53,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_43]),c_0_44])]),c_0_45])).

fof(c_0_57,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k2_relset_1(X29,X30,X31) = k2_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_58,plain,
    ( r2_hidden(esk3_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_44]),c_0_49]),c_0_50]),c_0_43])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(esk7_0))))
    | ~ r2_hidden(k1_funct_1(X1,esk3_3(k1_relat_1(X1),k2_relat_1(esk7_0),X1)),esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_62,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(X1),X2),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_56]),c_0_43])])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_43]),c_0_29])])).

cnf(c_0_65,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_3(k1_relat_1(k2_funct_1(esk6_0)),X1,k2_funct_1(esk6_0)),k1_relat_1(k2_funct_1(esk6_0)))
    | m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),X1)))
    | ~ v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_67,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_68,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_69,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | m1_subset_1(k2_relset_1(X23,X24,X25),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(esk7_0))))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(k1_funct_1(k2_funct_1(X1),esk3_3(k2_relat_1(X1),k2_relat_1(esk7_0),k2_funct_1(X1))),esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_54]),c_0_55])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k1_funct_1(k2_funct_1(esk6_0),X1),esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_49]),c_0_50]),c_0_64])])).

cnf(c_0_72,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_65]),c_0_43])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk3_3(k1_relat_1(k2_funct_1(esk6_0)),X1,k2_funct_1(esk6_0)),k1_relat_1(k2_funct_1(esk6_0)))
    | m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_54]),c_0_50]),c_0_64])])).

cnf(c_0_74,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0))))
    | ~ r2_hidden(esk3_3(esk5_0,k2_relat_1(esk7_0),k2_funct_1(esk6_0)),k1_relat_1(k2_funct_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_49]),c_0_50]),c_0_64]),c_0_72])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,X1,k2_funct_1(esk6_0)),esk5_0)
    | m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_61]),c_0_72]),c_0_72]),c_0_72]),c_0_49]),c_0_50]),c_0_64])])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_65])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_61]),c_0_72]),c_0_49]),c_0_50]),c_0_64])]),c_0_78])).

fof(c_0_82,plain,(
    ! [X19,X20] :
      ( ( r2_hidden(esk1_2(X19,X20),k1_relat_1(X19))
        | ~ v2_funct_1(X19)
        | k1_relat_1(X19) != k2_relat_1(X20)
        | k2_relat_1(X19) != k1_relat_1(X20)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(esk2_2(X19,X20),k1_relat_1(X20))
        | ~ v2_funct_1(X19)
        | k1_relat_1(X19) != k2_relat_1(X20)
        | k2_relat_1(X19) != k1_relat_1(X20)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( k1_funct_1(X19,esk1_2(X19,X20)) != esk2_2(X19,X20)
        | k1_funct_1(X20,esk2_2(X19,X20)) != esk1_2(X19,X20)
        | ~ v2_funct_1(X19)
        | k1_relat_1(X19) != k2_relat_1(X20)
        | k2_relat_1(X19) != k1_relat_1(X20)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( k1_funct_1(X19,esk1_2(X19,X20)) = esk2_2(X19,X20)
        | k1_funct_1(X20,esk2_2(X19,X20)) = esk1_2(X19,X20)
        | ~ v2_funct_1(X19)
        | k1_relat_1(X19) != k2_relat_1(X20)
        | k2_relat_1(X19) != k1_relat_1(X20)
        | X20 = k2_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_funct_1])])])])])).

cnf(c_0_83,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk7_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_22])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(k2_relat_1(k2_funct_1(esk6_0)),k1_zfmisc_1(k2_relat_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( k1_funct_1(X1,esk1_2(X1,X2)) = esk2_2(X1,X2)
    | k1_funct_1(X2,esk2_2(X1,X2)) = esk1_2(X1,X2)
    | X2 = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk4_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_relat_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_relat_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_53]),c_0_63]),c_0_49]),c_0_50]),c_0_64])])).

cnf(c_0_89,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_relat_1(X2))
    | X2 = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = X2
    | ~ r2_hidden(X2,esk5_0)
    | k1_funct_1(esk7_0,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_91,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_2(esk6_0,X1)) = esk2_2(esk6_0,X1)
    | k1_funct_1(X1,esk2_2(esk6_0,X1)) = esk1_2(esk6_0,X1)
    | X1 = k2_funct_1(esk6_0)
    | k2_relat_1(X1) != esk4_0
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_49]),c_0_63]),c_0_72]),c_0_50]),c_0_64])])).

cnf(c_0_92,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_93,negated_conjecture,
    ( esk7_0 != k2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_94,negated_conjecture,
    ( X1 = k2_funct_1(esk6_0)
    | r2_hidden(esk2_2(esk6_0,X1),k1_relat_1(X1))
    | k2_relat_1(X1) != esk4_0
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_49]),c_0_63]),c_0_72]),c_0_50]),c_0_64])])).

cnf(c_0_95,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_96,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(esk7_0,X1)) = X1
    | ~ r2_hidden(X1,esk5_0) ),
    inference(er,[status(thm)],[c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( k1_funct_1(esk7_0,esk2_2(esk6_0,esk7_0)) = esk1_2(esk6_0,esk7_0)
    | k1_funct_1(esk6_0,esk1_2(esk6_0,esk7_0)) = esk2_2(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_39]),c_0_37]),c_0_38])]),c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk7_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_92]),c_0_39]),c_0_39]),c_0_37]),c_0_38])]),c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( X1 = k2_funct_1(esk6_0)
    | r2_hidden(esk1_2(esk6_0,X1),esk4_0)
    | k2_relat_1(X1) != esk4_0
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_49]),c_0_63]),c_0_63]),c_0_72]),c_0_50]),c_0_64])])).

cnf(c_0_100,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_2(esk6_0,esk7_0)) = esk2_2(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk7_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_92]),c_0_39]),c_0_37]),c_0_38])]),c_0_93])).

cnf(c_0_102,plain,
    ( X2 = k2_funct_1(X1)
    | k1_funct_1(X1,esk1_2(X1,X2)) != esk2_2(X1,X2)
    | k1_funct_1(X2,esk2_2(X1,X2)) != esk1_2(X1,X2)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_103,negated_conjecture,
    ( k1_funct_1(esk7_0,esk2_2(esk6_0,esk7_0)) = esk1_2(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_100]),c_0_101])])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_100]),c_0_92]),c_0_63]),c_0_72]),c_0_39]),c_0_49]),c_0_37]),c_0_50]),c_0_38]),c_0_64])]),c_0_93]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 16:48:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t34_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))&![X5, X6]:(((r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6)=>(r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5))&((r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5)=>(r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_2)).
% 0.19/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.40  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 0.19/0.40  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 0.19/0.40  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.40  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.40  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.40  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.19/0.40  fof(t60_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((((v2_funct_1(X1)&k1_relat_1(X1)=k2_relat_1(X2))&k2_relat_1(X1)=k1_relat_1(X2))&![X3, X4]:((r2_hidden(X3,k1_relat_1(X1))&r2_hidden(X4,k1_relat_1(X2)))=>(k1_funct_1(X1,X3)=X4<=>k1_funct_1(X2,X4)=X3)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_1)).
% 0.19/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))&![X5, X6]:(((r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6)=>(r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5))&((r2_hidden(X6,X1)&k1_funct_1(X3,X6)=X5)=>(r2_hidden(X5,X2)&k1_funct_1(X4,X5)=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t34_funct_2])).
% 0.19/0.40  fof(c_0_16, plain, ![X32, X33, X34]:((((~v1_funct_2(X34,X32,X33)|X32=k1_relset_1(X32,X33,X34)|X33=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X32!=k1_relset_1(X32,X33,X34)|v1_funct_2(X34,X32,X33)|X33=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&((~v1_funct_2(X34,X32,X33)|X32=k1_relset_1(X32,X33,X34)|X32!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X32!=k1_relset_1(X32,X33,X34)|v1_funct_2(X34,X32,X33)|X32!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&((~v1_funct_2(X34,X32,X33)|X34=k1_xboole_0|X32=k1_xboole_0|X33!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X34!=k1_xboole_0|v1_funct_2(X34,X32,X33)|X32=k1_xboole_0|X33!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.40  fof(c_0_17, negated_conjecture, ![X47, X48]:(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk4_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))))&(((k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0&v2_funct_1(esk6_0))&(((r2_hidden(X48,esk4_0)|(~r2_hidden(X47,esk5_0)|k1_funct_1(esk7_0,X47)!=X48))&(k1_funct_1(esk6_0,X48)=X47|(~r2_hidden(X47,esk5_0)|k1_funct_1(esk7_0,X47)!=X48)))&((r2_hidden(X47,esk5_0)|(~r2_hidden(X48,esk4_0)|k1_funct_1(esk6_0,X48)!=X47))&(k1_funct_1(esk7_0,X47)=X48|(~r2_hidden(X48,esk4_0)|k1_funct_1(esk6_0,X48)!=X47)))))&((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk7_0!=k2_funct_1(esk6_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).
% 0.19/0.40  fof(c_0_18, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.40  fof(c_0_19, plain, ![X13, X14]:v1_relat_1(k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.40  fof(c_0_20, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k1_relset_1(X26,X27,X28)=k1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.40  cnf(c_0_21, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  fof(c_0_25, plain, ![X39, X40, X41]:((((v1_funct_1(X41)|(r2_hidden(esk3_3(X39,X40,X41),X39)|k1_relat_1(X41)!=X39)|(~v1_relat_1(X41)|~v1_funct_1(X41)))&(v1_funct_2(X41,X39,X40)|(r2_hidden(esk3_3(X39,X40,X41),X39)|k1_relat_1(X41)!=X39)|(~v1_relat_1(X41)|~v1_funct_1(X41))))&(m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|(r2_hidden(esk3_3(X39,X40,X41),X39)|k1_relat_1(X41)!=X39)|(~v1_relat_1(X41)|~v1_funct_1(X41))))&(((v1_funct_1(X41)|(~r2_hidden(k1_funct_1(X41,esk3_3(X39,X40,X41)),X40)|k1_relat_1(X41)!=X39)|(~v1_relat_1(X41)|~v1_funct_1(X41)))&(v1_funct_2(X41,X39,X40)|(~r2_hidden(k1_funct_1(X41,esk3_3(X39,X40,X41)),X40)|k1_relat_1(X41)!=X39)|(~v1_relat_1(X41)|~v1_funct_1(X41))))&(m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|(~r2_hidden(k1_funct_1(X41,esk3_3(X39,X40,X41)),X40)|k1_relat_1(X41)!=X39)|(~v1_relat_1(X41)|~v1_funct_1(X41))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.19/0.40  fof(c_0_26, plain, ![X16, X17]:(~v1_relat_1(X17)|~v1_funct_1(X17)|(~r2_hidden(X16,k1_relat_1(X17))|r2_hidden(k1_funct_1(X17,X16),k2_relat_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (k1_funct_1(esk7_0,X1)=X2|~r2_hidden(X2,esk4_0)|k1_funct_1(esk6_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_28, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_29, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (k1_relset_1(esk5_0,esk4_0,esk7_0)=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X2,esk4_0)|k1_funct_1(esk6_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  fof(c_0_33, plain, ![X35, X36, X37]:(((v1_funct_1(k2_funct_1(X37))|(~v2_funct_1(X37)|k2_relset_1(X35,X36,X37)!=X36)|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&(v1_funct_2(k2_funct_1(X37),X36,X35)|(~v2_funct_1(X37)|k2_relset_1(X35,X36,X37)!=X36)|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))))&(m1_subset_1(k2_funct_1(X37),k1_zfmisc_1(k2_zfmisc_1(X36,X35)))|(~v2_funct_1(X37)|k2_relset_1(X35,X36,X37)!=X36)|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.19/0.40  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(k1_funct_1(X1,esk3_3(X2,X3,X1)),X3)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_35, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))=X1|~r2_hidden(X1,esk4_0)), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_22]), c_0_29])])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_22])])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),esk5_0)|~r2_hidden(X1,esk4_0)), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.40  fof(c_0_41, plain, ![X18]:((k2_relat_1(X18)=k1_relat_1(k2_funct_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(k1_relat_1(X18)=k2_relat_1(k2_funct_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.40  fof(c_0_42, plain, ![X15]:((v1_relat_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(v1_funct_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|r2_hidden(esk3_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_47, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r2_hidden(k1_funct_1(X1,esk3_3(k1_relat_1(X1),X2,X1)),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk7_0))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])]), c_0_39]), c_0_40])).
% 0.19/0.40  cnf(c_0_53, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.40  cnf(c_0_54, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.40  cnf(c_0_55, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_43]), c_0_44])]), c_0_45])).
% 0.19/0.40  fof(c_0_57, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k2_relset_1(X29,X30,X31)=k2_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.40  cnf(c_0_58, plain, (r2_hidden(esk3_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (v1_funct_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_44]), c_0_49]), c_0_50]), c_0_43])])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(esk7_0))))|~r2_hidden(k1_funct_1(X1,esk3_3(k1_relat_1(X1),k2_relat_1(esk7_0),X1)),esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.40  cnf(c_0_61, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.40  cnf(c_0_62, plain, (r2_hidden(k1_funct_1(k2_funct_1(X1),X2),k1_relat_1(X1))|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_53]), c_0_54]), c_0_55])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_56]), c_0_43])])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_43]), c_0_29])])).
% 0.19/0.40  cnf(c_0_65, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_3(k1_relat_1(k2_funct_1(esk6_0)),X1,k2_funct_1(esk6_0)),k1_relat_1(k2_funct_1(esk6_0)))|m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),X1)))|~v1_relat_1(k2_funct_1(esk6_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.40  fof(c_0_67, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  fof(c_0_68, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.40  fof(c_0_69, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|m1_subset_1(k2_relset_1(X23,X24,X25),k1_zfmisc_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(esk7_0))))|~v2_funct_1(X1)|~r2_hidden(k1_funct_1(k2_funct_1(X1),esk3_3(k2_relat_1(X1),k2_relat_1(esk7_0),k2_funct_1(X1))),esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_54]), c_0_55])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (r2_hidden(k1_funct_1(k2_funct_1(esk6_0),X1),esk4_0)|~r2_hidden(X1,k1_relat_1(k2_funct_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_49]), c_0_50]), c_0_64])])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_65]), c_0_43])])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (r2_hidden(esk3_3(k1_relat_1(k2_funct_1(esk6_0)),X1,k2_funct_1(esk6_0)),k1_relat_1(k2_funct_1(esk6_0)))|m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk6_0)),X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_54]), c_0_50]), c_0_64])])).
% 0.19/0.40  cnf(c_0_74, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.40  cnf(c_0_75, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.40  cnf(c_0_76, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0))))|~r2_hidden(esk3_3(esk5_0,k2_relat_1(esk7_0),k2_funct_1(esk6_0)),k1_relat_1(k2_funct_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_49]), c_0_50]), c_0_64]), c_0_72])])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (r2_hidden(esk3_3(esk5_0,X1,k2_funct_1(esk6_0)),esk5_0)|m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_61]), c_0_72]), c_0_72]), c_0_72]), c_0_49]), c_0_50]), c_0_64])])).
% 0.19/0.40  cnf(c_0_79, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.40  cnf(c_0_80, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_76, c_0_65])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, (m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_relat_1(esk7_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_61]), c_0_72]), c_0_49]), c_0_50]), c_0_64])]), c_0_78])).
% 0.19/0.40  fof(c_0_82, plain, ![X19, X20]:(((r2_hidden(esk1_2(X19,X20),k1_relat_1(X19))|(~v2_funct_1(X19)|k1_relat_1(X19)!=k2_relat_1(X20)|k2_relat_1(X19)!=k1_relat_1(X20))|X20=k2_funct_1(X19)|(~v1_relat_1(X20)|~v1_funct_1(X20))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(r2_hidden(esk2_2(X19,X20),k1_relat_1(X20))|(~v2_funct_1(X19)|k1_relat_1(X19)!=k2_relat_1(X20)|k2_relat_1(X19)!=k1_relat_1(X20))|X20=k2_funct_1(X19)|(~v1_relat_1(X20)|~v1_funct_1(X20))|(~v1_relat_1(X19)|~v1_funct_1(X19))))&((k1_funct_1(X19,esk1_2(X19,X20))!=esk2_2(X19,X20)|k1_funct_1(X20,esk2_2(X19,X20))!=esk1_2(X19,X20)|(~v2_funct_1(X19)|k1_relat_1(X19)!=k2_relat_1(X20)|k2_relat_1(X19)!=k1_relat_1(X20))|X20=k2_funct_1(X19)|(~v1_relat_1(X20)|~v1_funct_1(X20))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(k1_funct_1(X19,esk1_2(X19,X20))=esk2_2(X19,X20)|k1_funct_1(X20,esk2_2(X19,X20))=esk1_2(X19,X20)|(~v2_funct_1(X19)|k1_relat_1(X19)!=k2_relat_1(X20)|k2_relat_1(X19)!=k1_relat_1(X20))|X20=k2_funct_1(X19)|(~v1_relat_1(X20)|~v1_funct_1(X20))|(~v1_relat_1(X19)|~v1_funct_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_funct_1])])])])])).
% 0.19/0.40  cnf(c_0_83, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_79, c_0_75])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (m1_subset_1(k2_relat_1(esk7_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_80, c_0_22])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (m1_subset_1(k2_relat_1(k2_funct_1(esk6_0)),k1_zfmisc_1(k2_relat_1(esk7_0)))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.40  cnf(c_0_86, plain, (k1_funct_1(X1,esk1_2(X1,X2))=esk2_2(X1,X2)|k1_funct_1(X2,esk2_2(X1,X2))=esk1_2(X1,X2)|X2=k2_funct_1(X1)|~v2_funct_1(X1)|k1_relat_1(X1)!=k2_relat_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, (k2_relat_1(esk7_0)=esk4_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_relat_1(esk7_0)))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_relat_1(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_53]), c_0_63]), c_0_49]), c_0_50]), c_0_64])])).
% 0.19/0.40  cnf(c_0_89, plain, (r2_hidden(esk2_2(X1,X2),k1_relat_1(X2))|X2=k2_funct_1(X1)|~v2_funct_1(X1)|k1_relat_1(X1)!=k2_relat_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.19/0.40  cnf(c_0_90, negated_conjecture, (k1_funct_1(esk6_0,X1)=X2|~r2_hidden(X2,esk5_0)|k1_funct_1(esk7_0,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_91, negated_conjecture, (k1_funct_1(esk6_0,esk1_2(esk6_0,X1))=esk2_2(esk6_0,X1)|k1_funct_1(X1,esk2_2(esk6_0,X1))=esk1_2(esk6_0,X1)|X1=k2_funct_1(esk6_0)|k2_relat_1(X1)!=esk4_0|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_49]), c_0_63]), c_0_72]), c_0_50]), c_0_64])])).
% 0.19/0.40  cnf(c_0_92, negated_conjecture, (k2_relat_1(esk7_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])])).
% 0.19/0.40  cnf(c_0_93, negated_conjecture, (esk7_0!=k2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_94, negated_conjecture, (X1=k2_funct_1(esk6_0)|r2_hidden(esk2_2(esk6_0,X1),k1_relat_1(X1))|k2_relat_1(X1)!=esk4_0|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_49]), c_0_63]), c_0_72]), c_0_50]), c_0_64])])).
% 0.19/0.40  cnf(c_0_95, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|X2=k2_funct_1(X1)|~v2_funct_1(X1)|k1_relat_1(X1)!=k2_relat_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.19/0.40  cnf(c_0_96, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(esk7_0,X1))=X1|~r2_hidden(X1,esk5_0)), inference(er,[status(thm)],[c_0_90])).
% 0.19/0.40  cnf(c_0_97, negated_conjecture, (k1_funct_1(esk7_0,esk2_2(esk6_0,esk7_0))=esk1_2(esk6_0,esk7_0)|k1_funct_1(esk6_0,esk1_2(esk6_0,esk7_0))=esk2_2(esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_39]), c_0_37]), c_0_38])]), c_0_93])).
% 0.19/0.40  cnf(c_0_98, negated_conjecture, (r2_hidden(esk2_2(esk6_0,esk7_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_92]), c_0_39]), c_0_39]), c_0_37]), c_0_38])]), c_0_93])).
% 0.19/0.40  cnf(c_0_99, negated_conjecture, (X1=k2_funct_1(esk6_0)|r2_hidden(esk1_2(esk6_0,X1),esk4_0)|k2_relat_1(X1)!=esk4_0|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_49]), c_0_63]), c_0_63]), c_0_72]), c_0_50]), c_0_64])])).
% 0.19/0.40  cnf(c_0_100, negated_conjecture, (k1_funct_1(esk6_0,esk1_2(esk6_0,esk7_0))=esk2_2(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])])).
% 0.19/0.40  cnf(c_0_101, negated_conjecture, (r2_hidden(esk1_2(esk6_0,esk7_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_92]), c_0_39]), c_0_37]), c_0_38])]), c_0_93])).
% 0.19/0.40  cnf(c_0_102, plain, (X2=k2_funct_1(X1)|k1_funct_1(X1,esk1_2(X1,X2))!=esk2_2(X1,X2)|k1_funct_1(X2,esk2_2(X1,X2))!=esk1_2(X1,X2)|~v2_funct_1(X1)|k1_relat_1(X1)!=k2_relat_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.19/0.40  cnf(c_0_103, negated_conjecture, (k1_funct_1(esk7_0,esk2_2(esk6_0,esk7_0))=esk1_2(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_100]), c_0_101])])).
% 0.19/0.40  cnf(c_0_104, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_100]), c_0_92]), c_0_63]), c_0_72]), c_0_39]), c_0_49]), c_0_37]), c_0_50]), c_0_38]), c_0_64])]), c_0_93]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 105
% 0.19/0.40  # Proof object clause steps            : 74
% 0.19/0.40  # Proof object formula steps           : 31
% 0.19/0.40  # Proof object conjectures             : 51
% 0.19/0.40  # Proof object clause conjectures      : 48
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 34
% 0.19/0.40  # Proof object initial formulas used   : 15
% 0.19/0.40  # Proof object generating inferences   : 34
% 0.19/0.40  # Proof object simplifying inferences  : 116
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 16
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 52
% 0.19/0.40  # Removed in clause preprocessing      : 3
% 0.19/0.40  # Initial clauses in saturation        : 49
% 0.19/0.40  # Processed clauses                    : 312
% 0.19/0.40  # ...of these trivial                  : 2
% 0.19/0.40  # ...subsumed                          : 30
% 0.19/0.40  # ...remaining for further processing  : 280
% 0.19/0.40  # Other redundant clauses eliminated   : 16
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 2
% 0.19/0.40  # Backward-rewritten                   : 50
% 0.19/0.40  # Generated clauses                    : 376
% 0.19/0.40  # ...of the previous two non-trivial   : 321
% 0.19/0.40  # Contextual simplify-reflections      : 42
% 0.19/0.40  # Paramodulations                      : 361
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 16
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
% 0.19/0.40  # Current number of processed clauses  : 166
% 0.19/0.40  #    Positive orientable unit clauses  : 34
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 3
% 0.19/0.40  #    Non-unit-clauses                  : 129
% 0.19/0.40  # Current number of unprocessed clauses: 98
% 0.19/0.40  # ...number of literals in the above   : 512
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 100
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 7933
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1220
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 74
% 0.19/0.40  # Unit Clause-clause subsumption calls : 95
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 27
% 0.19/0.40  # BW rewrite match successes           : 7
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 14633
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.059 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.063 s
% 0.19/0.40  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
