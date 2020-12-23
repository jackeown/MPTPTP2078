%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1079+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:42 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   49 (  78 expanded)
%              Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  343 ( 631 expanded)
%              Number of equality atoms :   31 (  52 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   34 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

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

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(fc10_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

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

fof(c_0_10,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | ~ r2_hidden(X37,X38)
      | X37 = k4_tarski(k1_mcart_1(X37),k2_mcart_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_11,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X39,X40)
      | v1_xboole_0(X40)
      | r2_hidden(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_12,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X21,X22,X23,X24] :
      ( v1_xboole_0(X21)
      | ~ v1_funct_1(X23)
      | ~ v1_funct_2(X23,X21,X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | ~ m1_subset_1(X24,X21)
      | m1_subset_1(k3_funct_2(X21,X22,X23,X24),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).

fof(c_0_15,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( X18 != k5_funct_2(X14,X15,X16,X17)
        | ~ m1_subset_1(X19,X14)
        | k3_funct_2(X14,X16,X18,X19) = k2_mcart_1(k3_funct_2(X14,k2_zfmisc_1(X15,X16),X17,X19))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X14,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X16)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16))))
        | v1_xboole_0(X16)
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) )
      & ( m1_subset_1(esk2_5(X14,X15,X16,X17,X18),X14)
        | X18 = k5_funct_2(X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X14,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X16)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16))))
        | v1_xboole_0(X16)
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) )
      & ( k3_funct_2(X14,X16,X18,esk2_5(X14,X15,X16,X17,X18)) != k2_mcart_1(k3_funct_2(X14,k2_zfmisc_1(X15,X16),X17,esk2_5(X14,X15,X16,X17,X18)))
        | X18 = k5_funct_2(X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X14,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,X16)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,k2_zfmisc_1(X15,X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,X16))))
        | v1_xboole_0(X16)
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_funct_2])])])])])])).

fof(c_0_16,plain,(
    ! [X29,X30,X31,X32] :
      ( ( v1_funct_1(k5_funct_2(X29,X30,X31,X32))
        | v1_xboole_0(X29)
        | v1_xboole_0(X30)
        | v1_xboole_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,k2_zfmisc_1(X30,X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,k2_zfmisc_1(X30,X31)))) )
      & ( v1_funct_2(k5_funct_2(X29,X30,X31,X32),X29,X31)
        | v1_xboole_0(X29)
        | v1_xboole_0(X30)
        | v1_xboole_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,k2_zfmisc_1(X30,X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,k2_zfmisc_1(X30,X31)))) )
      & ( m1_subset_1(k5_funct_2(X29,X30,X31,X32),k1_zfmisc_1(k2_zfmisc_1(X29,X31)))
        | v1_xboole_0(X29)
        | v1_xboole_0(X30)
        | v1_xboole_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,k2_zfmisc_1(X30,X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,k2_zfmisc_1(X30,X31)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_funct_2])])])])).

cnf(c_0_17,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | v1_xboole_0(X2)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_funct_1(k5_funct_2(X1,X2,X3,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v1_funct_2(k5_funct_2(X1,X2,X3,X4),X1,X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( m1_subset_1(k5_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X35,X36] : v1_relat_1(k2_zfmisc_1(X35,X36)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_24,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | v1_xboole_0(X34)
      | ~ v1_xboole_0(k2_zfmisc_1(X33,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc10_subset_1])])])).

fof(c_0_25,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( X11 != k4_funct_2(X7,X8,X9,X10)
        | ~ m1_subset_1(X12,X7)
        | k3_funct_2(X7,X8,X11,X12) = k1_mcart_1(k3_funct_2(X7,k2_zfmisc_1(X8,X9),X10,X12))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X7,X8)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,k2_zfmisc_1(X8,X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,k2_zfmisc_1(X8,X9))))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8)
        | v1_xboole_0(X7) )
      & ( m1_subset_1(esk1_5(X7,X8,X9,X10,X11),X7)
        | X11 = k4_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X7,X8)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,k2_zfmisc_1(X8,X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,k2_zfmisc_1(X8,X9))))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8)
        | v1_xboole_0(X7) )
      & ( k3_funct_2(X7,X8,X11,esk1_5(X7,X8,X9,X10,X11)) != k1_mcart_1(k3_funct_2(X7,k2_zfmisc_1(X8,X9),X10,esk1_5(X7,X8,X9,X10,X11)))
        | X11 = k4_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X7,X8)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,k2_zfmisc_1(X8,X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,k2_zfmisc_1(X8,X9))))
        | v1_xboole_0(X9)
        | v1_xboole_0(X8)
        | v1_xboole_0(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_funct_2])])])])])])).

fof(c_0_26,plain,(
    ! [X25,X26,X27,X28] :
      ( ( v1_funct_1(k4_funct_2(X25,X26,X27,X28))
        | v1_xboole_0(X25)
        | v1_xboole_0(X26)
        | v1_xboole_0(X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,k2_zfmisc_1(X26,X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,k2_zfmisc_1(X26,X27)))) )
      & ( v1_funct_2(k4_funct_2(X25,X26,X27,X28),X25,X26)
        | v1_xboole_0(X25)
        | v1_xboole_0(X26)
        | v1_xboole_0(X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,k2_zfmisc_1(X26,X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,k2_zfmisc_1(X26,X27)))) )
      & ( m1_subset_1(k4_funct_2(X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | v1_xboole_0(X25)
        | v1_xboole_0(X26)
        | v1_xboole_0(X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,k2_zfmisc_1(X26,X27))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,k2_zfmisc_1(X26,X27)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_funct_2])])])])).

fof(c_0_27,negated_conjecture,(
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

cnf(c_0_28,plain,
    ( k4_tarski(k1_mcart_1(k3_funct_2(X1,X2,X3,X4)),k2_mcart_1(k3_funct_2(X1,X2,X3,X4))) = k3_funct_2(X1,X2,X3,X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,X1)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_29,plain,
    ( k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5)) = k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ m1_subset_1(X5,X1)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v1_funct_1(k4_funct_2(X1,X2,X3,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( v1_funct_2(k4_funct_2(X1,X2,X3,X4),X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( m1_subset_1(k4_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k2_zfmisc_1(esk4_0,esk5_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))))
    & m1_subset_1(esk7_0,esk3_0)
    & k3_funct_2(esk3_0,k2_zfmisc_1(esk4_0,esk5_0),esk6_0,esk7_0) != k4_tarski(k3_funct_2(esk3_0,esk4_0,k4_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0),k3_funct_2(esk3_0,esk5_0,k5_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).

cnf(c_0_37,plain,
    ( k4_tarski(k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5)),k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5)) = k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ m1_subset_1(X5,X1)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_38,plain,
    ( k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5)) = k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ m1_subset_1(X5,X1)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k3_funct_2(esk3_0,k2_zfmisc_1(esk4_0,esk5_0),esk6_0,esk7_0) != k4_tarski(k3_funct_2(esk3_0,esk4_0,k4_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0),k3_funct_2(esk3_0,esk5_0,k5_funct_2(esk3_0,esk4_0,esk5_0,esk6_0),esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X5) = k4_tarski(k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X5),k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X5))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ m1_subset_1(X5,X1)
    | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
    | ~ v1_funct_1(X4) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk7_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])]),c_0_45]),c_0_46]),c_0_47]),
    [proof]).

%------------------------------------------------------------------------------
