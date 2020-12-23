%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:09 EST 2020

% Result     : Theorem 0.57s
% Output     : CNFRefutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 357 expanded)
%              Number of clauses        :   56 ( 164 expanded)
%              Number of leaves         :   14 (  96 expanded)
%              Depth                    :   23
%              Number of atoms          :  358 (1719 expanded)
%              Number of equality atoms :   46 ( 186 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t159_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(fc3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2) )
     => v1_xboole_0(k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(t121_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t142_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => r1_partfun1(k3_partfun1(k1_xboole_0,X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_partfun1)).

fof(dt_k3_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(k3_partfun1(X1,X2,X3))
        & m1_subset_1(k3_partfun1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_partfun1)).

fof(t45_ordinal1,axiom,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(t160_funct_2,conjecture,(
    ! [X1,X2] : k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).

fof(c_0_14,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X57,X58,X59] :
      ( ~ v1_funct_1(X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | r1_tarski(k5_partfun1(X57,X58,X59),k1_funct_2(X57,X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_funct_2])])).

fof(c_0_16,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ( ~ r2_hidden(esk3_2(X17,X18),X17)
        | ~ r2_hidden(esk3_2(X17,X18),X18)
        | X17 = X18 )
      & ( r2_hidden(esk3_2(X17,X18),X17)
        | r2_hidden(esk3_2(X17,X18),X18)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(k5_partfun1(X2,X3,X1),k1_funct_2(X2,X3))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X30,X31,X32,X33,X34,X36,X37,X38,X40] :
      ( ( v1_funct_1(esk4_5(X30,X31,X32,X33,X34))
        | ~ r2_hidden(X34,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( m1_subset_1(esk4_5(X30,X31,X32,X33,X34),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ r2_hidden(X34,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( esk4_5(X30,X31,X32,X33,X34) = X34
        | ~ r2_hidden(X34,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_partfun1(esk4_5(X30,X31,X32,X33,X34),X30)
        | ~ r2_hidden(X34,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( r1_partfun1(X32,esk4_5(X30,X31,X32,X33,X34))
        | ~ r2_hidden(X34,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | X37 != X36
        | ~ v1_partfun1(X37,X30)
        | ~ r1_partfun1(X32,X37)
        | r2_hidden(X36,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( ~ r2_hidden(esk5_4(X30,X31,X32,X38),X38)
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | X40 != esk5_4(X30,X31,X32,X38)
        | ~ v1_partfun1(X40,X30)
        | ~ r1_partfun1(X32,X40)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_funct_1(esk6_4(X30,X31,X32,X38))
        | r2_hidden(esk5_4(X30,X31,X32,X38),X38)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( m1_subset_1(esk6_4(X30,X31,X32,X38),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | r2_hidden(esk5_4(X30,X31,X32,X38),X38)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( esk6_4(X30,X31,X32,X38) = esk5_4(X30,X31,X32,X38)
        | r2_hidden(esk5_4(X30,X31,X32,X38),X38)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_partfun1(esk6_4(X30,X31,X32,X38),X30)
        | r2_hidden(esk5_4(X30,X31,X32,X38),X38)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( r1_partfun1(X32,esk6_4(X30,X31,X32,X38))
        | r2_hidden(esk5_4(X30,X31,X32,X38),X38)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_funct_2(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( X1 = X2
    | r2_hidden(esk3_2(X1,X2),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( v1_partfun1(esk4_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( esk4_5(X1,X2,X3,X4,X5) = X5
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r2_hidden(esk3_2(X1,X2),X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k5_partfun1(X1,X2,X3) = X4
    | r2_hidden(esk3_2(k5_partfun1(X1,X2,X3),X4),k1_funct_2(X1,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_xboole_0(X4) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X45,X46] :
      ( v1_xboole_0(X45)
      | ~ v1_xboole_0(X46)
      | v1_xboole_0(k1_funct_2(X45,X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).

fof(c_0_30,plain,(
    ! [X27,X28,X29] :
      ( ( v1_funct_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | v1_xboole_0(X28) )
      & ( v1_partfun1(X29,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | v1_xboole_0(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_31,plain,(
    ! [X47,X48,X49] :
      ( ( v1_funct_1(X49)
        | ~ r2_hidden(X49,k1_funct_2(X47,X48)) )
      & ( v1_funct_2(X49,X47,X48)
        | ~ r2_hidden(X49,k1_funct_2(X47,X48)) )
      & ( m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ r2_hidden(X49,k1_funct_2(X47,X48)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).

cnf(c_0_32,plain,
    ( v1_partfun1(X1,X2)
    | X3 != k5_partfun1(X2,X4,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X5)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( k5_partfun1(X1,X2,X3) = k1_funct_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_xboole_0(k1_funct_2(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k1_funct_2(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v1_partfun1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X4,X3)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k5_partfun1(X1,X2,X3) = k1_funct_2(X1,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_43,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_xboole_0(X24)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_partfun1(X26,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk1_1(k1_funct_2(X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(k1_funct_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_47,plain,
    ( v1_funct_1(esk1_1(k1_funct_2(X1,X2)))
    | v1_xboole_0(k1_funct_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_42])).

cnf(c_0_48,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( m1_subset_1(esk2_2(k1_funct_2(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_funct_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_20])).

cnf(c_0_52,plain,
    ( v1_partfun1(esk2_2(k1_funct_2(X1,X2),X3),X1)
    | r1_tarski(k1_funct_2(X1,X2),X3)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_53,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | v1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(X3,X4,X5)
    | ~ r1_partfun1(X5,X1)
    | ~ v1_partfun1(X1,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( v1_funct_1(esk2_2(k1_funct_2(X1,X2),X3))
    | r1_tarski(k1_funct_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_44])).

cnf(c_0_56,plain,
    ( v1_partfun1(esk2_2(k1_funct_2(X1,X2),X3),X1)
    | r1_tarski(k1_funct_2(X1,X2),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_52])).

fof(c_0_57,plain,(
    ! [X50,X51,X52] :
      ( ~ v1_relat_1(X52)
      | ~ v1_funct_1(X52)
      | r1_partfun1(k3_partfun1(k1_xboole_0,X50,X51),X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_partfun1])])).

cnf(c_0_58,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_funct_2(X1,X2),X3)
    | r2_hidden(esk2_2(k1_funct_2(X1,X2),X3),X4)
    | X4 != k5_partfun1(X1,X2,X5)
    | ~ r1_partfun1(X5,esk2_2(k1_funct_2(X1,X2),X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_49]),c_0_55]),c_0_56])).

cnf(c_0_60,plain,
    ( r1_partfun1(k3_partfun1(k1_xboole_0,X2,X3),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,plain,
    ( v1_relat_1(esk2_2(k1_funct_2(X1,X2),X3))
    | r1_tarski(k1_funct_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_58,c_0_49])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_funct_2(X1,X2),X3)
    | r2_hidden(esk2_2(k1_funct_2(X1,X2),X3),X4)
    | X4 != k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X5,X6))
    | ~ m1_subset_1(k3_partfun1(k1_xboole_0,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,X5,X6)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_55])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_funct_2(X1,X2),X3)
    | r2_hidden(esk2_2(k1_funct_2(X1,X2),X3),k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X4,X5)))
    | ~ m1_subset_1(k3_partfun1(k1_xboole_0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,X4,X5)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_funct_2(X1,X2),k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X3,X4)))
    | ~ m1_subset_1(k3_partfun1(k1_xboole_0,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X4,X5)))
    | ~ m1_subset_1(k3_partfun1(k1_xboole_0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,X4,X5))
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_65])).

fof(c_0_67,plain,(
    ! [X42,X43,X44] :
      ( ( v1_funct_1(k3_partfun1(X42,X43,X44))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( m1_subset_1(k3_partfun1(X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_partfun1])])])).

fof(c_0_68,plain,(
    ! [X20] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X20)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[t45_ordinal1])).

cnf(c_0_69,plain,
    ( X1 = k1_funct_2(X2,X3)
    | r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X4,X5)))
    | r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),X1)
    | ~ m1_subset_1(k3_partfun1(k1_xboole_0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,X4,X5)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_21])).

cnf(c_0_70,plain,
    ( m1_subset_1(k3_partfun1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_71,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_72,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,plain,
    ( X1 = k1_funct_2(X2,X3)
    | r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))
    | r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),X1)
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72])])).

cnf(c_0_74,plain,
    ( v1_funct_1(k3_partfun1(X1,X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( X1 = k1_funct_2(X2,X3)
    | r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))
    | r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_71]),c_0_72])])).

fof(c_0_76,negated_conjecture,(
    ~ ! [X1,X2] : k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    inference(assume_negation,[status(cth)],[t160_funct_2])).

cnf(c_0_77,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2)
    | r2_hidden(esk3_2(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)),k1_funct_2(X1,X2)),k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(ef,[status(thm)],[c_0_75])).

fof(c_0_78,negated_conjecture,(
    k5_partfun1(esk7_0,esk8_0,k3_partfun1(k1_xboole_0,esk7_0,esk8_0)) != k1_funct_2(esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).

cnf(c_0_79,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2)
    | r2_hidden(esk3_2(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)),k1_funct_2(X1,X2)),k1_funct_2(X1,X2))
    | ~ m1_subset_1(k3_partfun1(k1_xboole_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( k5_partfun1(esk7_0,esk8_0,k3_partfun1(k1_xboole_0,esk7_0,esk8_0)) != k1_funct_2(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_81,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2)
    | ~ m1_subset_1(k3_partfun1(k1_xboole_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_79]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(k3_partfun1(k1_xboole_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_funct_1(k3_partfun1(k1_xboole_0,esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_70]),c_0_71]),c_0_72])])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_74]),c_0_71]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:56:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.57/0.75  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.57/0.75  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.57/0.75  #
% 0.57/0.75  # Preprocessing time       : 0.029 s
% 0.57/0.75  # Presaturation interreduction done
% 0.57/0.75  
% 0.57/0.75  # Proof found!
% 0.57/0.75  # SZS status Theorem
% 0.57/0.75  # SZS output start CNFRefutation
% 0.57/0.75  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.57/0.75  fof(t159_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_funct_2)).
% 0.57/0.75  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.57/0.75  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.57/0.75  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 0.57/0.75  fof(fc3_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_xboole_0(X2))=>v1_xboole_0(k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 0.57/0.75  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.57/0.75  fof(t121_funct_2, axiom, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.57/0.75  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.57/0.75  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.57/0.75  fof(t142_partfun1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>r1_partfun1(k3_partfun1(k1_xboole_0,X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_partfun1)).
% 0.57/0.75  fof(dt_k3_partfun1, axiom, ![X1, X2, X3]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_funct_1(k3_partfun1(X1,X2,X3))&m1_subset_1(k3_partfun1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_partfun1)).
% 0.57/0.75  fof(t45_ordinal1, axiom, ![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 0.57/0.75  fof(t160_funct_2, conjecture, ![X1, X2]:k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_funct_2)).
% 0.57/0.75  fof(c_0_14, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.57/0.75  fof(c_0_15, plain, ![X57, X58, X59]:(~v1_funct_1(X59)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|r1_tarski(k5_partfun1(X57,X58,X59),k1_funct_2(X57,X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_funct_2])])).
% 0.57/0.75  fof(c_0_16, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.57/0.75  fof(c_0_17, plain, ![X17, X18]:((~r2_hidden(esk3_2(X17,X18),X17)|~r2_hidden(esk3_2(X17,X18),X18)|X17=X18)&(r2_hidden(esk3_2(X17,X18),X17)|r2_hidden(esk3_2(X17,X18),X18)|X17=X18)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.57/0.75  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.57/0.75  cnf(c_0_19, plain, (r1_tarski(k5_partfun1(X2,X3,X1),k1_funct_2(X2,X3))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.57/0.75  cnf(c_0_20, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.57/0.75  cnf(c_0_21, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.57/0.75  fof(c_0_22, plain, ![X30, X31, X32, X33, X34, X36, X37, X38, X40]:(((((((v1_funct_1(esk4_5(X30,X31,X32,X33,X34))|~r2_hidden(X34,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(m1_subset_1(esk4_5(X30,X31,X32,X33,X34),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~r2_hidden(X34,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(esk4_5(X30,X31,X32,X33,X34)=X34|~r2_hidden(X34,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(v1_partfun1(esk4_5(X30,X31,X32,X33,X34),X30)|~r2_hidden(X34,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(r1_partfun1(X32,esk4_5(X30,X31,X32,X33,X34))|~r2_hidden(X34,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|X37!=X36|~v1_partfun1(X37,X30)|~r1_partfun1(X32,X37)|r2_hidden(X36,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&((~r2_hidden(esk5_4(X30,X31,X32,X38),X38)|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|X40!=esk5_4(X30,X31,X32,X38)|~v1_partfun1(X40,X30)|~r1_partfun1(X32,X40))|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(((((v1_funct_1(esk6_4(X30,X31,X32,X38))|r2_hidden(esk5_4(X30,X31,X32,X38),X38)|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(m1_subset_1(esk6_4(X30,X31,X32,X38),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|r2_hidden(esk5_4(X30,X31,X32,X38),X38)|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(esk6_4(X30,X31,X32,X38)=esk5_4(X30,X31,X32,X38)|r2_hidden(esk5_4(X30,X31,X32,X38),X38)|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(v1_partfun1(esk6_4(X30,X31,X32,X38),X30)|r2_hidden(esk5_4(X30,X31,X32,X38),X38)|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(r1_partfun1(X32,esk6_4(X30,X31,X32,X38))|r2_hidden(esk5_4(X30,X31,X32,X38),X38)|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.57/0.75  cnf(c_0_23, plain, (r2_hidden(X1,k1_funct_2(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.57/0.75  cnf(c_0_24, plain, (X1=X2|r2_hidden(esk3_2(X1,X2),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.57/0.75  cnf(c_0_25, plain, (v1_partfun1(esk4_5(X1,X2,X3,X4,X5),X1)|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.57/0.75  cnf(c_0_26, plain, (esk4_5(X1,X2,X3,X4,X5)=X5|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.57/0.75  cnf(c_0_27, plain, (X1=X2|~r2_hidden(esk3_2(X1,X2),X1)|~r2_hidden(esk3_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.57/0.75  cnf(c_0_28, plain, (k5_partfun1(X1,X2,X3)=X4|r2_hidden(esk3_2(k5_partfun1(X1,X2,X3),X4),k1_funct_2(X1,X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_xboole_0(X4)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.57/0.75  fof(c_0_29, plain, ![X45, X46]:(v1_xboole_0(X45)|~v1_xboole_0(X46)|v1_xboole_0(k1_funct_2(X45,X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).
% 0.57/0.75  fof(c_0_30, plain, ![X27, X28, X29]:((v1_funct_1(X29)|(~v1_funct_1(X29)|~v1_funct_2(X29,X27,X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_xboole_0(X28))&(v1_partfun1(X29,X27)|(~v1_funct_1(X29)|~v1_funct_2(X29,X27,X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_xboole_0(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.57/0.75  fof(c_0_31, plain, ![X47, X48, X49]:(((v1_funct_1(X49)|~r2_hidden(X49,k1_funct_2(X47,X48)))&(v1_funct_2(X49,X47,X48)|~r2_hidden(X49,k1_funct_2(X47,X48))))&(m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|~r2_hidden(X49,k1_funct_2(X47,X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).
% 0.57/0.75  cnf(c_0_32, plain, (v1_partfun1(X1,X2)|X3!=k5_partfun1(X2,X4,X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~v1_funct_1(X5)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.57/0.75  cnf(c_0_33, plain, (k5_partfun1(X1,X2,X3)=k1_funct_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_xboole_0(k1_funct_2(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_24])).
% 0.57/0.75  cnf(c_0_34, plain, (v1_xboole_0(X1)|v1_xboole_0(k1_funct_2(X1,X2))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.57/0.75  cnf(c_0_35, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.57/0.75  cnf(c_0_36, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.57/0.75  cnf(c_0_37, plain, (v1_funct_1(X1)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.57/0.75  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.57/0.75  cnf(c_0_39, plain, (v1_partfun1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~v1_funct_1(X3)|~r2_hidden(X1,k5_partfun1(X2,X4,X3))), inference(er,[status(thm)],[c_0_32])).
% 0.57/0.75  cnf(c_0_40, plain, (k5_partfun1(X1,X2,X3)=k1_funct_2(X1,X2)|v1_xboole_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.57/0.75  cnf(c_0_41, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])).
% 0.57/0.75  cnf(c_0_42, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.57/0.75  fof(c_0_43, plain, ![X24, X25, X26]:(~v1_xboole_0(X24)|(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_partfun1(X26,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.57/0.75  cnf(c_0_44, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.57/0.75  cnf(c_0_45, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~v1_funct_1(X3)|~r2_hidden(X1,k1_funct_2(X2,X4))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.57/0.75  cnf(c_0_46, plain, (m1_subset_1(esk1_1(k1_funct_2(X1,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|v1_xboole_0(k1_funct_2(X1,X2))), inference(spm,[status(thm)],[c_0_38, c_0_42])).
% 0.57/0.75  cnf(c_0_47, plain, (v1_funct_1(esk1_1(k1_funct_2(X1,X2)))|v1_xboole_0(k1_funct_2(X1,X2))), inference(spm,[status(thm)],[c_0_37, c_0_42])).
% 0.57/0.75  cnf(c_0_48, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.57/0.75  cnf(c_0_49, plain, (m1_subset_1(esk2_2(k1_funct_2(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|r1_tarski(k1_funct_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_38, c_0_44])).
% 0.57/0.75  cnf(c_0_50, plain, (r2_hidden(X4,X6)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X1!=X4|~v1_partfun1(X1,X2)|~r1_partfun1(X5,X1)|X6!=k5_partfun1(X2,X3,X5)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.57/0.75  cnf(c_0_51, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_20])).
% 0.57/0.75  cnf(c_0_52, plain, (v1_partfun1(esk2_2(k1_funct_2(X1,X2),X3),X1)|r1_tarski(k1_funct_2(X1,X2),X3)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.57/0.75  fof(c_0_53, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|v1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.57/0.75  cnf(c_0_54, plain, (r2_hidden(X1,X2)|X2!=k5_partfun1(X3,X4,X5)|~r1_partfun1(X5,X1)|~v1_partfun1(X1,X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X5)|~v1_funct_1(X1)), inference(er,[status(thm)],[c_0_50])).
% 0.57/0.75  cnf(c_0_55, plain, (v1_funct_1(esk2_2(k1_funct_2(X1,X2),X3))|r1_tarski(k1_funct_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_37, c_0_44])).
% 0.57/0.75  cnf(c_0_56, plain, (v1_partfun1(esk2_2(k1_funct_2(X1,X2),X3),X1)|r1_tarski(k1_funct_2(X1,X2),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_44]), c_0_52])).
% 0.57/0.75  fof(c_0_57, plain, ![X50, X51, X52]:(~v1_relat_1(X52)|~v1_funct_1(X52)|r1_partfun1(k3_partfun1(k1_xboole_0,X50,X51),X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_partfun1])])).
% 0.57/0.75  cnf(c_0_58, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.57/0.75  cnf(c_0_59, plain, (r1_tarski(k1_funct_2(X1,X2),X3)|r2_hidden(esk2_2(k1_funct_2(X1,X2),X3),X4)|X4!=k5_partfun1(X1,X2,X5)|~r1_partfun1(X5,esk2_2(k1_funct_2(X1,X2),X3))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_49]), c_0_55]), c_0_56])).
% 0.57/0.75  cnf(c_0_60, plain, (r1_partfun1(k3_partfun1(k1_xboole_0,X2,X3),X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.57/0.75  cnf(c_0_61, plain, (v1_relat_1(esk2_2(k1_funct_2(X1,X2),X3))|r1_tarski(k1_funct_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_58, c_0_49])).
% 0.57/0.75  cnf(c_0_62, plain, (r1_tarski(k1_funct_2(X1,X2),X3)|r2_hidden(esk2_2(k1_funct_2(X1,X2),X3),X4)|X4!=k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X5,X6))|~m1_subset_1(k3_partfun1(k1_xboole_0,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(k3_partfun1(k1_xboole_0,X5,X6))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_55])).
% 0.57/0.75  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.57/0.75  cnf(c_0_64, plain, (r1_tarski(k1_funct_2(X1,X2),X3)|r2_hidden(esk2_2(k1_funct_2(X1,X2),X3),k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X4,X5)))|~m1_subset_1(k3_partfun1(k1_xboole_0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(k3_partfun1(k1_xboole_0,X4,X5))), inference(er,[status(thm)],[c_0_62])).
% 0.57/0.75  cnf(c_0_65, plain, (r1_tarski(k1_funct_2(X1,X2),k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X3,X4)))|~m1_subset_1(k3_partfun1(k1_xboole_0,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(k3_partfun1(k1_xboole_0,X3,X4))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.57/0.75  cnf(c_0_66, plain, (r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X4,X5)))|~m1_subset_1(k3_partfun1(k1_xboole_0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(k3_partfun1(k1_xboole_0,X4,X5))|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(spm,[status(thm)],[c_0_18, c_0_65])).
% 0.57/0.75  fof(c_0_67, plain, ![X42, X43, X44]:((v1_funct_1(k3_partfun1(X42,X43,X44))|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(m1_subset_1(k3_partfun1(X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|(~v1_relat_1(X42)|~v1_funct_1(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_partfun1])])])).
% 0.57/0.75  fof(c_0_68, plain, ![X20]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X20))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), inference(variable_rename,[status(thm)],[t45_ordinal1])).
% 0.57/0.75  cnf(c_0_69, plain, (X1=k1_funct_2(X2,X3)|r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X4,X5)))|r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),X1)|~m1_subset_1(k3_partfun1(k1_xboole_0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(k3_partfun1(k1_xboole_0,X4,X5))), inference(spm,[status(thm)],[c_0_66, c_0_21])).
% 0.57/0.75  cnf(c_0_70, plain, (m1_subset_1(k3_partfun1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.57/0.75  cnf(c_0_71, plain, (v1_funct_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.57/0.75  cnf(c_0_72, plain, (v1_relat_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.57/0.75  cnf(c_0_73, plain, (X1=k1_funct_2(X2,X3)|r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))|r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),X1)|~v1_funct_1(k3_partfun1(k1_xboole_0,X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_72])])).
% 0.57/0.75  cnf(c_0_74, plain, (v1_funct_1(k3_partfun1(X1,X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.57/0.75  cnf(c_0_75, plain, (X1=k1_funct_2(X2,X3)|r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))|r2_hidden(esk3_2(X1,k1_funct_2(X2,X3)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_71]), c_0_72])])).
% 0.57/0.75  fof(c_0_76, negated_conjecture, ~(![X1, X2]:k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2)), inference(assume_negation,[status(cth)],[t160_funct_2])).
% 0.57/0.75  cnf(c_0_77, plain, (k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2)|r2_hidden(esk3_2(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)),k1_funct_2(X1,X2)),k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))), inference(ef,[status(thm)],[c_0_75])).
% 0.57/0.75  fof(c_0_78, negated_conjecture, k5_partfun1(esk7_0,esk8_0,k3_partfun1(k1_xboole_0,esk7_0,esk8_0))!=k1_funct_2(esk7_0,esk8_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).
% 0.57/0.75  cnf(c_0_79, plain, (k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2)|r2_hidden(esk3_2(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)),k1_funct_2(X1,X2)),k1_funct_2(X1,X2))|~m1_subset_1(k3_partfun1(k1_xboole_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(k3_partfun1(k1_xboole_0,X1,X2))), inference(spm,[status(thm)],[c_0_23, c_0_77])).
% 0.57/0.75  cnf(c_0_80, negated_conjecture, (k5_partfun1(esk7_0,esk8_0,k3_partfun1(k1_xboole_0,esk7_0,esk8_0))!=k1_funct_2(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.57/0.75  cnf(c_0_81, plain, (k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2)|~m1_subset_1(k3_partfun1(k1_xboole_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(k3_partfun1(k1_xboole_0,X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_79]), c_0_77])).
% 0.57/0.75  cnf(c_0_82, negated_conjecture, (~m1_subset_1(k3_partfun1(k1_xboole_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))|~v1_funct_1(k3_partfun1(k1_xboole_0,esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.57/0.75  cnf(c_0_83, negated_conjecture, (~v1_funct_1(k3_partfun1(k1_xboole_0,esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_70]), c_0_71]), c_0_72])])).
% 0.57/0.75  cnf(c_0_84, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_74]), c_0_71]), c_0_72])]), ['proof']).
% 0.57/0.75  # SZS output end CNFRefutation
% 0.57/0.75  # Proof object total steps             : 85
% 0.57/0.75  # Proof object clause steps            : 56
% 0.57/0.75  # Proof object formula steps           : 29
% 0.57/0.75  # Proof object conjectures             : 7
% 0.57/0.75  # Proof object clause conjectures      : 4
% 0.57/0.75  # Proof object formula conjectures     : 3
% 0.57/0.75  # Proof object initial clauses used    : 24
% 0.57/0.75  # Proof object initial formulas used   : 14
% 0.57/0.75  # Proof object generating inferences   : 31
% 0.57/0.75  # Proof object simplifying inferences  : 25
% 0.57/0.75  # Training examples: 0 positive, 0 negative
% 0.57/0.75  # Parsed axioms                        : 16
% 0.57/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.57/0.75  # Initial clauses                      : 40
% 0.57/0.75  # Removed in clause preprocessing      : 1
% 0.57/0.75  # Initial clauses in saturation        : 39
% 0.57/0.75  # Processed clauses                    : 2865
% 0.57/0.75  # ...of these trivial                  : 12
% 0.57/0.75  # ...subsumed                          : 2072
% 0.57/0.75  # ...remaining for further processing  : 781
% 0.57/0.75  # Other redundant clauses eliminated   : 1
% 0.57/0.75  # Clauses deleted for lack of memory   : 0
% 0.57/0.75  # Backward-subsumed                    : 156
% 0.57/0.75  # Backward-rewritten                   : 0
% 0.57/0.75  # Generated clauses                    : 11458
% 0.57/0.75  # ...of the previous two non-trivial   : 11116
% 0.57/0.75  # Contextual simplify-reflections      : 221
% 0.57/0.75  # Paramodulations                      : 11359
% 0.57/0.75  # Factorizations                       : 20
% 0.57/0.75  # Equation resolutions                 : 79
% 0.57/0.75  # Propositional unsat checks           : 0
% 0.57/0.75  #    Propositional check models        : 0
% 0.57/0.75  #    Propositional check unsatisfiable : 0
% 0.57/0.75  #    Propositional clauses             : 0
% 0.57/0.75  #    Propositional clauses after purity: 0
% 0.57/0.75  #    Propositional unsat core size     : 0
% 0.57/0.75  #    Propositional preprocessing time  : 0.000
% 0.57/0.75  #    Propositional encoding time       : 0.000
% 0.57/0.75  #    Propositional solver time         : 0.000
% 0.57/0.75  #    Success case prop preproc time    : 0.000
% 0.57/0.75  #    Success case prop encoding time   : 0.000
% 0.57/0.75  #    Success case prop solver time     : 0.000
% 0.57/0.75  # Current number of processed clauses  : 585
% 0.57/0.75  #    Positive orientable unit clauses  : 6
% 0.57/0.75  #    Positive unorientable unit clauses: 0
% 0.57/0.75  #    Negative unit clauses             : 2
% 0.57/0.75  #    Non-unit-clauses                  : 577
% 0.57/0.75  # Current number of unprocessed clauses: 7719
% 0.57/0.75  # ...number of literals in the above   : 76665
% 0.57/0.75  # Current number of archived formulas  : 0
% 0.57/0.75  # Current number of archived clauses   : 195
% 0.57/0.75  # Clause-clause subsumption calls (NU) : 186951
% 0.57/0.75  # Rec. Clause-clause subsumption calls : 18337
% 0.57/0.75  # Non-unit clause-clause subsumptions  : 2449
% 0.57/0.75  # Unit Clause-clause subsumption calls : 8
% 0.57/0.75  # Rewrite failures with RHS unbound    : 0
% 0.57/0.75  # BW rewrite match attempts            : 3
% 0.57/0.75  # BW rewrite match successes           : 0
% 0.57/0.75  # Condensation attempts                : 0
% 0.57/0.75  # Condensation successes               : 0
% 0.57/0.75  # Termbank termtop insertions          : 318276
% 0.57/0.75  
% 0.57/0.75  # -------------------------------------------------
% 0.57/0.75  # User time                : 0.409 s
% 0.57/0.75  # System time              : 0.006 s
% 0.57/0.75  # Total time               : 0.415 s
% 0.57/0.75  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
