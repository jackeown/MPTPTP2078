%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:19 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 177 expanded)
%              Number of clauses        :   36 (  59 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  376 (1218 expanded)
%              Number of equality atoms :   38 ( 128 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   34 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t189_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                 => r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t196_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5) = k4_tarski(k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5),k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_funct_2)).

fof(d7_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X1,X3)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) )
                     => ( X5 = k5_funct_2(X1,X2,X3,X4)
                      <=> ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => k3_funct_2(X1,X3,X5,X6) = k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_funct_2)).

fof(dt_k5_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X3)
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
     => ( v1_funct_1(k5_funct_2(X1,X2,X3,X4))
        & v1_funct_2(k5_funct_2(X1,X2,X3,X4),X1,X3)
        & m1_subset_1(k5_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_funct_2)).

fof(d6_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X1,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                     => ( X5 = k4_funct_2(X1,X2,X3,X4)
                      <=> ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => k3_funct_2(X1,X2,X5,X6) = k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_funct_2)).

fof(dt_k4_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X3)
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
     => ( v1_funct_1(k4_funct_2(X1,X2,X3,X4))
        & v1_funct_2(k4_funct_2(X1,X2,X3,X4),X1,X2)
        & m1_subset_1(k4_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_funct_2)).

fof(fc10_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

fof(fc9_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
     => v1_relat_1(k2_relat_1(X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relset_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(c_0_11,plain,(
    ! [X44,X45,X46,X47] :
      ( v1_xboole_0(X44)
      | v1_xboole_0(X45)
      | ~ m1_subset_1(X46,X44)
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,X44,X45)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | r2_hidden(k3_funct_2(X44,X45,X47,X46),k2_relset_1(X44,X45,X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).

fof(c_0_12,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k2_relset_1(X9,X10,X11) = k2_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))
    | ~ m1_subset_1(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X40,X41,X42,X43] :
      ( v1_xboole_0(X40)
      | ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,X40,X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | ~ m1_subset_1(X43,X40)
      | k3_funct_2(X40,X41,X42,X43) = k1_funct_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5) = k4_tarski(k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5),k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t196_funct_2])).

cnf(c_0_17,plain,
    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),k2_relat_1(X3))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k2_zfmisc_1(esk4_0,esk5_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))))
    & m1_subset_1(esk7_0,esk3_0)
    & k3_funct_2(esk3_0,k2_zfmisc_1(esk4_0,esk5_0),esk6_0,esk7_0) != k4_tarski(k3_funct_2(esk3_0,esk4_0,k4_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0),k3_funct_2(esk3_0,esk5_0,k5_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_20,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( X25 != k5_funct_2(X21,X22,X23,X24)
        | ~ m1_subset_1(X26,X21)
        | k3_funct_2(X21,X23,X25,X26) = k2_mcart_1(k3_funct_2(X21,k2_zfmisc_1(X22,X23),X24,X26))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X21,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X23)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,k2_zfmisc_1(X22,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,k2_zfmisc_1(X22,X23))))
        | v1_xboole_0(X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X21) )
      & ( m1_subset_1(esk2_5(X21,X22,X23,X24,X25),X21)
        | X25 = k5_funct_2(X21,X22,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X21,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X23)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,k2_zfmisc_1(X22,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,k2_zfmisc_1(X22,X23))))
        | v1_xboole_0(X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X21) )
      & ( k3_funct_2(X21,X23,X25,esk2_5(X21,X22,X23,X24,X25)) != k2_mcart_1(k3_funct_2(X21,k2_zfmisc_1(X22,X23),X24,esk2_5(X21,X22,X23,X24,X25)))
        | X25 = k5_funct_2(X21,X22,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X21,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X23)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,k2_zfmisc_1(X22,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,k2_zfmisc_1(X22,X23))))
        | v1_xboole_0(X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_funct_2])])])])])])).

fof(c_0_21,plain,(
    ! [X32,X33,X34,X35] :
      ( ( v1_funct_1(k5_funct_2(X32,X33,X34,X35))
        | v1_xboole_0(X32)
        | v1_xboole_0(X33)
        | v1_xboole_0(X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,k2_zfmisc_1(X33,X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,k2_zfmisc_1(X33,X34)))) )
      & ( v1_funct_2(k5_funct_2(X32,X33,X34,X35),X32,X34)
        | v1_xboole_0(X32)
        | v1_xboole_0(X33)
        | v1_xboole_0(X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,k2_zfmisc_1(X33,X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,k2_zfmisc_1(X33,X34)))) )
      & ( m1_subset_1(k5_funct_2(X32,X33,X34,X35),k1_zfmisc_1(k2_zfmisc_1(X32,X34)))
        | v1_xboole_0(X32)
        | v1_xboole_0(X33)
        | v1_xboole_0(X34)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X32,k2_zfmisc_1(X33,X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,k2_zfmisc_1(X33,X34)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_funct_2])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ v1_funct_2(X1,X4,X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X2,X4) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k3_funct_2(X2,X4,X1,X6) = k2_mcart_1(k3_funct_2(X2,k2_zfmisc_1(X3,X4),X5,X6))
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | X1 != k5_funct_2(X2,X3,X4,X5)
    | ~ m1_subset_1(X6,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X2,k2_zfmisc_1(X3,X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( m1_subset_1(k5_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v1_funct_1(k5_funct_2(X1,X2,X3,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_funct_2(k5_funct_2(X1,X2,X3,X4),X1,X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( X18 != k4_funct_2(X14,X15,X16,X17)
        | ~ m1_subset_1(X19,X14)
        | k3_funct_2(X14,X15,X18,X19) = k1_mcart_1(k3_funct_2(X14,k2_zfmisc_1(X15,X16),X17,X19))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X14,X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16))))
        | v1_xboole_0(X16)
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) )
      & ( m1_subset_1(esk1_5(X14,X15,X16,X17,X18),X14)
        | X18 = k4_funct_2(X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X14,X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16))))
        | v1_xboole_0(X16)
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) )
      & ( k3_funct_2(X14,X15,X18,esk1_5(X14,X15,X16,X17,X18)) != k1_mcart_1(k3_funct_2(X14,k2_zfmisc_1(X15,X16),X17,esk1_5(X14,X15,X16,X17,X18)))
        | X18 = k4_funct_2(X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X14,X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16))))
        | v1_xboole_0(X16)
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_funct_2])])])])])])).

fof(c_0_32,plain,(
    ! [X28,X29,X30,X31] :
      ( ( v1_funct_1(k4_funct_2(X28,X29,X30,X31))
        | v1_xboole_0(X28)
        | v1_xboole_0(X29)
        | v1_xboole_0(X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,k2_zfmisc_1(X29,X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,k2_zfmisc_1(X29,X30)))) )
      & ( v1_funct_2(k4_funct_2(X28,X29,X30,X31),X28,X29)
        | v1_xboole_0(X28)
        | v1_xboole_0(X29)
        | v1_xboole_0(X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,k2_zfmisc_1(X29,X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,k2_zfmisc_1(X29,X30)))) )
      & ( m1_subset_1(k4_funct_2(X28,X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | v1_xboole_0(X28)
        | v1_xboole_0(X29)
        | v1_xboole_0(X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,k2_zfmisc_1(X29,X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,k2_zfmisc_1(X29,X30)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_funct_2])])])])).

fof(c_0_33,plain,(
    ! [X7,X8] :
      ( v1_xboole_0(X7)
      | v1_xboole_0(X8)
      | ~ v1_xboole_0(k2_zfmisc_1(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc10_subset_1])])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),k2_relat_1(esk6_0))
    | v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk7_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_36,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,k2_zfmisc_1(X37,X38))))
      | v1_relat_1(k2_relat_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_relset_1])])).

cnf(c_0_37,negated_conjecture,
    ( k3_funct_2(esk3_0,k2_zfmisc_1(esk4_0,esk5_0),esk6_0,esk7_0) != k4_tarski(k3_funct_2(esk3_0,esk4_0,k4_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0),k3_funct_2(esk3_0,esk5_0,k5_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,plain,
    ( k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5)) = k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ m1_subset_1(X5,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_39,plain,
    ( k3_funct_2(X2,X3,X1,X6) = k1_mcart_1(k3_funct_2(X2,k2_zfmisc_1(X3,X4),X5,X6))
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | X1 != k4_funct_2(X2,X3,X4,X5)
    | ~ m1_subset_1(X6,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X2,k2_zfmisc_1(X3,X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4)))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( m1_subset_1(k4_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( v1_funct_1(k4_funct_2(X1,X2,X3,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( v1_funct_2(k4_funct_2(X1,X2,X3,X4),X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_43,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ r2_hidden(X12,X13)
      | X12 = k4_tarski(k1_mcart_1(X12),k2_mcart_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk7_0),k2_relat_1(esk6_0))
    | v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( v1_relat_1(k2_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4)))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( k4_tarski(k3_funct_2(esk3_0,esk4_0,k4_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0),k3_funct_2(esk3_0,esk5_0,k5_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)) != k1_funct_1(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_23]),c_0_24]),c_0_25]),c_0_35])]),c_0_26])).

cnf(c_0_50,plain,
    ( k3_funct_2(X1,X2,k5_funct_2(X1,X3,X2,X4),X5) = k2_mcart_1(k1_funct_1(X4,X5))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X3,X2))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X3,X2))))
    | ~ m1_subset_1(X5,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_18])).

cnf(c_0_51,plain,
    ( k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5)) = k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ m1_subset_1(X5,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_52,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk7_0),k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( k4_tarski(k3_funct_2(esk3_0,esk4_0,k4_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0),k2_mcart_1(k1_funct_1(esk6_0,esk7_0))) != k1_funct_1(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_23]),c_0_24]),c_0_25]),c_0_35])]),c_0_46]),c_0_47]),c_0_26])).

cnf(c_0_56,plain,
    ( k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5) = k1_mcart_1(k1_funct_1(X4,X5))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ m1_subset_1(X5,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_18])).

cnf(c_0_57,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_funct_1(esk6_0,esk7_0)),k2_mcart_1(k1_funct_1(esk6_0,esk7_0))) = k1_funct_1(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_23]),c_0_24]),c_0_25]),c_0_35])]),c_0_46]),c_0_47]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.14/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.028 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t189_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 0.14/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.14/0.39  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.14/0.39  fof(t196_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))))=>![X5]:(m1_subset_1(X5,X1)=>k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5)=k4_tarski(k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5),k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t196_funct_2)).
% 0.14/0.39  fof(d7_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))=>(X5=k5_funct_2(X1,X2,X3,X4)<=>![X6]:(m1_subset_1(X6,X1)=>k3_funct_2(X1,X3,X5,X6)=k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_funct_2)).
% 0.14/0.39  fof(dt_k5_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&v1_funct_1(X4))&v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))))=>((v1_funct_1(k5_funct_2(X1,X2,X3,X4))&v1_funct_2(k5_funct_2(X1,X2,X3,X4),X1,X3))&m1_subset_1(k5_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_funct_2)).
% 0.14/0.39  fof(d6_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(X5=k4_funct_2(X1,X2,X3,X4)<=>![X6]:(m1_subset_1(X6,X1)=>k3_funct_2(X1,X2,X5,X6)=k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_funct_2)).
% 0.14/0.39  fof(dt_k4_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&v1_funct_1(X4))&v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))))=>((v1_funct_1(k4_funct_2(X1,X2,X3,X4))&v1_funct_2(k4_funct_2(X1,X2,X3,X4),X1,X2))&m1_subset_1(k4_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_funct_2)).
% 0.14/0.39  fof(fc10_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>~(v1_xboole_0(k2_zfmisc_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_subset_1)).
% 0.14/0.39  fof(fc9_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))=>v1_relat_1(k2_relat_1(X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relset_1)).
% 0.14/0.39  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.14/0.39  fof(c_0_11, plain, ![X44, X45, X46, X47]:(v1_xboole_0(X44)|(v1_xboole_0(X45)|(~m1_subset_1(X46,X44)|(~v1_funct_1(X47)|~v1_funct_2(X47,X44,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|r2_hidden(k3_funct_2(X44,X45,X47,X46),k2_relset_1(X44,X45,X47)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).
% 0.14/0.39  fof(c_0_12, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|k2_relset_1(X9,X10,X11)=k2_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.14/0.39  cnf(c_0_13, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))|~m1_subset_1(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_14, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  fof(c_0_15, plain, ![X40, X41, X42, X43]:(v1_xboole_0(X40)|~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~m1_subset_1(X43,X40)|k3_funct_2(X40,X41,X42,X43)=k1_funct_1(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.14/0.39  fof(c_0_16, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))))=>![X5]:(m1_subset_1(X5,X1)=>k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5)=k4_tarski(k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5),k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5)))))))), inference(assume_negation,[status(cth)],[t196_funct_2])).
% 0.14/0.39  cnf(c_0_17, plain, (r2_hidden(k3_funct_2(X1,X2,X3,X4),k2_relat_1(X3))|v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.39  cnf(c_0_18, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  fof(c_0_19, negated_conjecture, (~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,k2_zfmisc_1(esk4_0,esk5_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)))))&(m1_subset_1(esk7_0,esk3_0)&k3_funct_2(esk3_0,k2_zfmisc_1(esk4_0,esk5_0),esk6_0,esk7_0)!=k4_tarski(k3_funct_2(esk3_0,esk4_0,k4_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0),k3_funct_2(esk3_0,esk5_0,k5_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.14/0.39  fof(c_0_20, plain, ![X21, X22, X23, X24, X25, X26]:((X25!=k5_funct_2(X21,X22,X23,X24)|(~m1_subset_1(X26,X21)|k3_funct_2(X21,X23,X25,X26)=k2_mcart_1(k3_funct_2(X21,k2_zfmisc_1(X22,X23),X24,X26)))|(~v1_funct_1(X25)|~v1_funct_2(X25,X21,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X23))))|(~v1_funct_1(X24)|~v1_funct_2(X24,X21,k2_zfmisc_1(X22,X23))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,k2_zfmisc_1(X22,X23)))))|v1_xboole_0(X23)|v1_xboole_0(X22)|v1_xboole_0(X21))&((m1_subset_1(esk2_5(X21,X22,X23,X24,X25),X21)|X25=k5_funct_2(X21,X22,X23,X24)|(~v1_funct_1(X25)|~v1_funct_2(X25,X21,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X23))))|(~v1_funct_1(X24)|~v1_funct_2(X24,X21,k2_zfmisc_1(X22,X23))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,k2_zfmisc_1(X22,X23)))))|v1_xboole_0(X23)|v1_xboole_0(X22)|v1_xboole_0(X21))&(k3_funct_2(X21,X23,X25,esk2_5(X21,X22,X23,X24,X25))!=k2_mcart_1(k3_funct_2(X21,k2_zfmisc_1(X22,X23),X24,esk2_5(X21,X22,X23,X24,X25)))|X25=k5_funct_2(X21,X22,X23,X24)|(~v1_funct_1(X25)|~v1_funct_2(X25,X21,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X23))))|(~v1_funct_1(X24)|~v1_funct_2(X24,X21,k2_zfmisc_1(X22,X23))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,k2_zfmisc_1(X22,X23)))))|v1_xboole_0(X23)|v1_xboole_0(X22)|v1_xboole_0(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_funct_2])])])])])])).
% 0.14/0.39  fof(c_0_21, plain, ![X32, X33, X34, X35]:(((v1_funct_1(k5_funct_2(X32,X33,X34,X35))|(v1_xboole_0(X32)|v1_xboole_0(X33)|v1_xboole_0(X34)|~v1_funct_1(X35)|~v1_funct_2(X35,X32,k2_zfmisc_1(X33,X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,k2_zfmisc_1(X33,X34))))))&(v1_funct_2(k5_funct_2(X32,X33,X34,X35),X32,X34)|(v1_xboole_0(X32)|v1_xboole_0(X33)|v1_xboole_0(X34)|~v1_funct_1(X35)|~v1_funct_2(X35,X32,k2_zfmisc_1(X33,X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,k2_zfmisc_1(X33,X34)))))))&(m1_subset_1(k5_funct_2(X32,X33,X34,X35),k1_zfmisc_1(k2_zfmisc_1(X32,X34)))|(v1_xboole_0(X32)|v1_xboole_0(X33)|v1_xboole_0(X34)|~v1_funct_1(X35)|~v1_funct_2(X35,X32,k2_zfmisc_1(X33,X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,k2_zfmisc_1(X33,X34))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_funct_2])])])])).
% 0.14/0.39  cnf(c_0_22, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X1,X4,X3)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X2,X4)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.39  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_26, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_27, plain, (k3_funct_2(X2,X4,X1,X6)=k2_mcart_1(k3_funct_2(X2,k2_zfmisc_1(X3,X4),X5,X6))|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|X1!=k5_funct_2(X2,X3,X4,X5)|~m1_subset_1(X6,X2)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,X2,k2_zfmisc_1(X3,X4))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_28, plain, (m1_subset_1(k5_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_29, plain, (v1_funct_1(k5_funct_2(X1,X2,X3,X4))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_30, plain, (v1_funct_2(k5_funct_2(X1,X2,X3,X4),X1,X3)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  fof(c_0_31, plain, ![X14, X15, X16, X17, X18, X19]:((X18!=k4_funct_2(X14,X15,X16,X17)|(~m1_subset_1(X19,X14)|k3_funct_2(X14,X15,X18,X19)=k1_mcart_1(k3_funct_2(X14,k2_zfmisc_1(X15,X16),X17,X19)))|(~v1_funct_1(X18)|~v1_funct_2(X18,X14,X15)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))|(~v1_funct_1(X17)|~v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16)))))|v1_xboole_0(X16)|v1_xboole_0(X15)|v1_xboole_0(X14))&((m1_subset_1(esk1_5(X14,X15,X16,X17,X18),X14)|X18=k4_funct_2(X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,X14,X15)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))|(~v1_funct_1(X17)|~v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16)))))|v1_xboole_0(X16)|v1_xboole_0(X15)|v1_xboole_0(X14))&(k3_funct_2(X14,X15,X18,esk1_5(X14,X15,X16,X17,X18))!=k1_mcart_1(k3_funct_2(X14,k2_zfmisc_1(X15,X16),X17,esk1_5(X14,X15,X16,X17,X18)))|X18=k4_funct_2(X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,X14,X15)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))|(~v1_funct_1(X17)|~v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16)))))|v1_xboole_0(X16)|v1_xboole_0(X15)|v1_xboole_0(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_funct_2])])])])])])).
% 0.14/0.39  fof(c_0_32, plain, ![X28, X29, X30, X31]:(((v1_funct_1(k4_funct_2(X28,X29,X30,X31))|(v1_xboole_0(X28)|v1_xboole_0(X29)|v1_xboole_0(X30)|~v1_funct_1(X31)|~v1_funct_2(X31,X28,k2_zfmisc_1(X29,X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,k2_zfmisc_1(X29,X30))))))&(v1_funct_2(k4_funct_2(X28,X29,X30,X31),X28,X29)|(v1_xboole_0(X28)|v1_xboole_0(X29)|v1_xboole_0(X30)|~v1_funct_1(X31)|~v1_funct_2(X31,X28,k2_zfmisc_1(X29,X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,k2_zfmisc_1(X29,X30)))))))&(m1_subset_1(k4_funct_2(X28,X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|(v1_xboole_0(X28)|v1_xboole_0(X29)|v1_xboole_0(X30)|~v1_funct_1(X31)|~v1_funct_2(X31,X28,k2_zfmisc_1(X29,X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,k2_zfmisc_1(X29,X30))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_funct_2])])])])).
% 0.14/0.39  fof(c_0_33, plain, ![X7, X8]:(v1_xboole_0(X7)|v1_xboole_0(X8)|~v1_xboole_0(k2_zfmisc_1(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc10_subset_1])])])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),k2_relat_1(esk6_0))|v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))|~m1_subset_1(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk7_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  fof(c_0_36, plain, ![X36, X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,k2_zfmisc_1(X37,X38))))|v1_relat_1(k2_relat_1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_relset_1])])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (k3_funct_2(esk3_0,k2_zfmisc_1(esk4_0,esk5_0),esk6_0,esk7_0)!=k4_tarski(k3_funct_2(esk3_0,esk4_0,k4_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0),k3_funct_2(esk3_0,esk5_0,k5_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_38, plain, (k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5))=k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))|~m1_subset_1(X5,X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.14/0.39  cnf(c_0_39, plain, (k3_funct_2(X2,X3,X1,X6)=k1_mcart_1(k3_funct_2(X2,k2_zfmisc_1(X3,X4),X5,X6))|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|X1!=k4_funct_2(X2,X3,X4,X5)|~m1_subset_1(X6,X2)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X5)|~v1_funct_2(X5,X2,k2_zfmisc_1(X3,X4))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_40, plain, (m1_subset_1(k4_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  cnf(c_0_41, plain, (v1_funct_1(k4_funct_2(X1,X2,X3,X4))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  cnf(c_0_42, plain, (v1_funct_2(k4_funct_2(X1,X2,X3,X4),X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.39  fof(c_0_43, plain, ![X12, X13]:(~v1_relat_1(X13)|(~r2_hidden(X12,X13)|X12=k4_tarski(k1_mcart_1(X12),k2_mcart_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.14/0.39  cnf(c_0_44, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_xboole_0(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk7_0),k2_relat_1(esk6_0))|v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_48, plain, (v1_relat_1(k2_relat_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4))))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (k4_tarski(k3_funct_2(esk3_0,esk4_0,k4_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0),k3_funct_2(esk3_0,esk5_0,k5_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0))!=k1_funct_1(esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_23]), c_0_24]), c_0_25]), c_0_35])]), c_0_26])).
% 0.14/0.39  cnf(c_0_50, plain, (k3_funct_2(X1,X2,k5_funct_2(X1,X3,X2,X4),X5)=k2_mcart_1(k1_funct_1(X4,X5))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X1)|~v1_funct_2(X4,X1,k2_zfmisc_1(X3,X2))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X3,X2))))|~m1_subset_1(X5,X1)), inference(spm,[status(thm)],[c_0_38, c_0_18])).
% 0.14/0.39  cnf(c_0_51, plain, (k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5))=k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))|~m1_subset_1(X5,X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.14/0.39  cnf(c_0_52, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.39  cnf(c_0_53, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk7_0),k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])).
% 0.14/0.39  cnf(c_0_54, negated_conjecture, (v1_relat_1(k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_48, c_0_25])).
% 0.14/0.39  cnf(c_0_55, negated_conjecture, (k4_tarski(k3_funct_2(esk3_0,esk4_0,k4_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0),k2_mcart_1(k1_funct_1(esk6_0,esk7_0)))!=k1_funct_1(esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_23]), c_0_24]), c_0_25]), c_0_35])]), c_0_46]), c_0_47]), c_0_26])).
% 0.14/0.39  cnf(c_0_56, plain, (k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5)=k1_mcart_1(k1_funct_1(X4,X5))|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))|~m1_subset_1(X5,X1)), inference(spm,[status(thm)],[c_0_51, c_0_18])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, (k4_tarski(k1_mcart_1(k1_funct_1(esk6_0,esk7_0)),k2_mcart_1(k1_funct_1(esk6_0,esk7_0)))=k1_funct_1(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_23]), c_0_24]), c_0_25]), c_0_35])]), c_0_46]), c_0_47]), c_0_26]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 59
% 0.14/0.39  # Proof object clause steps            : 36
% 0.14/0.39  # Proof object formula steps           : 23
% 0.14/0.39  # Proof object conjectures             : 19
% 0.14/0.39  # Proof object clause conjectures      : 16
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 22
% 0.14/0.39  # Proof object initial formulas used   : 11
% 0.14/0.39  # Proof object generating inferences   : 14
% 0.14/0.39  # Proof object simplifying inferences  : 37
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 11
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 26
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 26
% 0.14/0.39  # Processed clauses                    : 106
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 12
% 0.14/0.39  # ...remaining for further processing  : 94
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 2
% 0.14/0.39  # Backward-rewritten                   : 1
% 0.14/0.39  # Generated clauses                    : 95
% 0.14/0.39  # ...of the previous two non-trivial   : 82
% 0.14/0.39  # Contextual simplify-reflections      : 16
% 0.14/0.39  # Paramodulations                      : 93
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 2
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 65
% 0.14/0.39  #    Positive orientable unit clauses  : 7
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 6
% 0.14/0.39  #    Non-unit-clauses                  : 52
% 0.14/0.39  # Current number of unprocessed clauses: 26
% 0.14/0.39  # ...number of literals in the above   : 332
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 29
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 3462
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 113
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 29
% 0.14/0.39  # Unit Clause-clause subsumption calls : 40
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 1
% 0.14/0.39  # BW rewrite match successes           : 1
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 9467
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.044 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.047 s
% 0.14/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
