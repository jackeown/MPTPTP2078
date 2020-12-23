%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 856 expanded)
%              Number of clauses        :   62 ( 356 expanded)
%              Number of leaves         :   16 ( 221 expanded)
%              Depth                    :   18
%              Number of atoms          :  472 (5000 expanded)
%              Number of equality atoms :   40 ( 426 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   56 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(d13_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fraenkel_a_2_1_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_1_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t8_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t45_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k2_orders_2(X1,k1_struct_0(X1)) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_orders_2)).

fof(d2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k1_struct_0(X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_16,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | ~ v1_xboole_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v3_orders_2(X35)
      | ~ v4_orders_2(X35)
      | ~ v5_orders_2(X35)
      | ~ l1_orders_2(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | m1_subset_1(k2_orders_2(X35,X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ v3_orders_2(X33)
      | ~ v4_orders_2(X33)
      | ~ v5_orders_2(X33)
      | ~ l1_orders_2(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | k2_orders_2(X33,X34) = a_2_1_orders_2(X33,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

fof(c_0_21,plain,(
    ! [X30,X31] :
      ( ~ r2_hidden(X30,X31)
      | ~ r1_tarski(X31,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_22,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_23,plain,(
    ! [X38,X39,X40,X42,X43] :
      ( ( m1_subset_1(esk3_3(X38,X39,X40),u1_struct_0(X39))
        | ~ r2_hidden(X38,a_2_1_orders_2(X39,X40))
        | v2_struct_0(X39)
        | ~ v3_orders_2(X39)
        | ~ v4_orders_2(X39)
        | ~ v5_orders_2(X39)
        | ~ l1_orders_2(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))) )
      & ( X38 = esk3_3(X38,X39,X40)
        | ~ r2_hidden(X38,a_2_1_orders_2(X39,X40))
        | v2_struct_0(X39)
        | ~ v3_orders_2(X39)
        | ~ v4_orders_2(X39)
        | ~ v5_orders_2(X39)
        | ~ l1_orders_2(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))) )
      & ( ~ m1_subset_1(X42,u1_struct_0(X39))
        | ~ r2_hidden(X42,X40)
        | r2_orders_2(X39,esk3_3(X38,X39,X40),X42)
        | ~ r2_hidden(X38,a_2_1_orders_2(X39,X40))
        | v2_struct_0(X39)
        | ~ v3_orders_2(X39)
        | ~ v4_orders_2(X39)
        | ~ v5_orders_2(X39)
        | ~ l1_orders_2(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))) )
      & ( m1_subset_1(esk4_4(X38,X39,X40,X43),u1_struct_0(X39))
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | X38 != X43
        | r2_hidden(X38,a_2_1_orders_2(X39,X40))
        | v2_struct_0(X39)
        | ~ v3_orders_2(X39)
        | ~ v4_orders_2(X39)
        | ~ v5_orders_2(X39)
        | ~ l1_orders_2(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))) )
      & ( r2_hidden(esk4_4(X38,X39,X40,X43),X40)
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | X38 != X43
        | r2_hidden(X38,a_2_1_orders_2(X39,X40))
        | v2_struct_0(X39)
        | ~ v3_orders_2(X39)
        | ~ v4_orders_2(X39)
        | ~ v5_orders_2(X39)
        | ~ l1_orders_2(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))) )
      & ( ~ r2_orders_2(X39,X43,esk4_4(X38,X39,X40,X43))
        | ~ m1_subset_1(X43,u1_struct_0(X39))
        | X38 != X43
        | r2_hidden(X38,a_2_1_orders_2(X39,X40))
        | v2_struct_0(X39)
        | ~ v3_orders_2(X39)
        | ~ v4_orders_2(X39)
        | ~ v5_orders_2(X39)
        | ~ l1_orders_2(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

fof(c_0_24,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X16,X15)
        | r2_hidden(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ r2_hidden(X16,X15)
        | m1_subset_1(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ m1_subset_1(X16,X15)
        | v1_xboole_0(X16)
        | ~ v1_xboole_0(X15) )
      & ( ~ v1_xboole_0(X16)
        | m1_subset_1(X16,X15)
        | ~ v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ r2_hidden(X3,k2_orders_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X3)
    | r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | X1 != X4
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ r2_hidden(X3,a_2_1_orders_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk4_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_3(X2,X1,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_38,plain,
    ( X1 = esk3_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_39,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | m1_subset_1(X24,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_1_orders_2(X1,k1_xboole_0))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

fof(c_0_41,plain,(
    ! [X18,X19,X20] :
      ( ( m1_subset_1(esk2_3(X18,X19,X20),X18)
        | X19 = X20
        | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(X18)) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X19 = X20
        | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(X18)) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X19 = X20
        | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

fof(c_0_42,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k2_orders_2(X1,k1_struct_0(X1)) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t45_orders_2])).

fof(c_0_46,plain,(
    ! [X32] :
      ( ~ l1_struct_0(X32)
      | k1_struct_0(X32) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).

fof(c_0_47,plain,(
    ! [X37] :
      ( ~ l1_orders_2(X37)
      | l1_struct_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_40]),c_0_36])])).

cnf(c_0_49,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_36])])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k2_orders_2(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_19])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & k2_orders_2(esk5_0,k1_struct_0(esk5_0)) != u1_struct_0(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_45])])])])).

cnf(c_0_55,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( X1 = X2
    | v2_struct_0(X3)
    | ~ l1_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v3_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v1_xboole_0(u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_58,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk1_2(X2,u1_struct_0(X1)),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk1_2(k2_orders_2(X1,X2),X3),u1_struct_0(X1))
    | r1_tarski(k2_orders_2(X1,X2),X3)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k2_orders_2(esk5_0,k1_struct_0(esk5_0)) != u1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( X1 = k2_orders_2(X2,X3)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_xboole_0(u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_19])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | r1_tarski(k2_orders_2(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_68,negated_conjecture,
    ( k2_orders_2(esk5_0,k1_xboole_0) != u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_69,plain,
    ( k2_orders_2(X1,X2) = k2_orders_2(X1,X3)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_71,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_72,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_74,plain,
    ( k2_orders_2(X1,X2) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(u1_struct_0(X1),k2_orders_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X2,a_2_1_orders_2(X1,k1_xboole_0))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(esk1_2(X2,a_2_1_orders_2(X1,k1_xboole_0)),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | v1_xboole_0(X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_53])).

cnf(c_0_77,negated_conjecture,
    ( k2_orders_2(esk5_0,X1) != u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_63]),c_0_70]),c_0_71]),c_0_72]),c_0_36])]),c_0_73])).

cnf(c_0_78,plain,
    ( a_2_1_orders_2(X1,X2) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(u1_struct_0(X1),a_2_1_orders_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_26])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | r1_tarski(u1_struct_0(X1),a_2_1_orders_2(X1,k1_xboole_0))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_81,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_82,negated_conjecture,
    ( a_2_1_orders_2(esk5_0,X1) != u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_26]),c_0_63]),c_0_70]),c_0_71]),c_0_72])]),c_0_73])).

cnf(c_0_83,plain,
    ( a_2_1_orders_2(X1,k1_xboole_0) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_36])])).

cnf(c_0_84,negated_conjecture,
    ( a_2_1_orders_2(esk5_0,k1_xboole_0) != u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_26]),c_0_63]),c_0_70]),c_0_71]),c_0_72]),c_0_36])]),c_0_73])).

cnf(c_0_85,plain,
    ( m1_subset_1(X1,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( a_2_1_orders_2(esk5_0,X1) != u1_struct_0(esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_63]),c_0_70]),c_0_71]),c_0_72])]),c_0_84]),c_0_73])).

cnf(c_0_87,plain,
    ( a_2_1_orders_2(X1,k1_xboole_0) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | m1_subset_1(u1_struct_0(X1),k1_xboole_0)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_83])).

cnf(c_0_88,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_36]),c_0_63]),c_0_70]),c_0_71]),c_0_72])]),c_0_73])).

cnf(c_0_90,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_81])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_92]),c_0_63]),c_0_70]),c_0_71]),c_0_72]),c_0_90])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:33:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.50  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.028 s
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.50  fof(dt_k2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 0.19/0.50  fof(d13_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 0.19/0.50  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.50  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.50  fof(fraenkel_a_2_1_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_1_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 0.19/0.50  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.50  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.50  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.50  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 0.19/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.50  fof(t45_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k2_orders_2(X1,k1_struct_0(X1))=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_orders_2)).
% 0.19/0.50  fof(d2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k1_struct_0(X1)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 0.19/0.50  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.50  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.50  fof(c_0_16, plain, ![X27, X28, X29]:(~r2_hidden(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(X29))|~v1_xboole_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.50  fof(c_0_17, plain, ![X35, X36]:(v2_struct_0(X35)|~v3_orders_2(X35)|~v4_orders_2(X35)|~v5_orders_2(X35)|~l1_orders_2(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|m1_subset_1(k2_orders_2(X35,X36),k1_zfmisc_1(u1_struct_0(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).
% 0.19/0.50  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_19, plain, (v2_struct_0(X1)|m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.50  fof(c_0_20, plain, ![X33, X34]:(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|k2_orders_2(X33,X34)=a_2_1_orders_2(X33,X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).
% 0.19/0.50  fof(c_0_21, plain, ![X30, X31]:(~r2_hidden(X30,X31)|~r1_tarski(X31,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.50  fof(c_0_22, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.50  fof(c_0_23, plain, ![X38, X39, X40, X42, X43]:((((m1_subset_1(esk3_3(X38,X39,X40),u1_struct_0(X39))|~r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))))&(X38=esk3_3(X38,X39,X40)|~r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))))))&(~m1_subset_1(X42,u1_struct_0(X39))|(~r2_hidden(X42,X40)|r2_orders_2(X39,esk3_3(X38,X39,X40),X42))|~r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))))))&((m1_subset_1(esk4_4(X38,X39,X40,X43),u1_struct_0(X39))|(~m1_subset_1(X43,u1_struct_0(X39))|X38!=X43)|r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))))&((r2_hidden(esk4_4(X38,X39,X40,X43),X40)|(~m1_subset_1(X43,u1_struct_0(X39))|X38!=X43)|r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))))&(~r2_orders_2(X39,X43,esk4_4(X38,X39,X40,X43))|(~m1_subset_1(X43,u1_struct_0(X39))|X38!=X43)|r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).
% 0.19/0.50  fof(c_0_24, plain, ![X15, X16]:(((~m1_subset_1(X16,X15)|r2_hidden(X16,X15)|v1_xboole_0(X15))&(~r2_hidden(X16,X15)|m1_subset_1(X16,X15)|v1_xboole_0(X15)))&((~m1_subset_1(X16,X15)|v1_xboole_0(X16)|~v1_xboole_0(X15))&(~v1_xboole_0(X16)|m1_subset_1(X16,X15)|~v1_xboole_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.50  cnf(c_0_25, plain, (v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(u1_struct_0(X1))|~r2_hidden(X3,k2_orders_2(X1,X2))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.50  cnf(c_0_26, plain, (v2_struct_0(X1)|k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.50  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.50  cnf(c_0_28, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.50  cnf(c_0_29, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_1_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  fof(c_0_30, plain, ![X17]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.50  cnf(c_0_31, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.50  cnf(c_0_32, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  cnf(c_0_33, plain, (v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(u1_struct_0(X1))|~r2_hidden(X3,a_2_1_orders_2(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.50  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.50  cnf(c_0_35, plain, (v2_struct_0(X1)|r2_hidden(esk4_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.50  cnf(c_0_36, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.50  cnf(c_0_37, plain, (v2_struct_0(X1)|r2_hidden(esk3_3(X2,X1,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,a_2_1_orders_2(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.19/0.50  cnf(c_0_38, plain, (X1=esk3_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  fof(c_0_39, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|m1_subset_1(X24,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.50  cnf(c_0_40, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_1_orders_2(X1,k1_xboole_0))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.19/0.50  fof(c_0_41, plain, ![X18, X19, X20]:((m1_subset_1(esk2_3(X18,X19,X20),X18)|X19=X20|~m1_subset_1(X20,k1_zfmisc_1(X18))|~m1_subset_1(X19,k1_zfmisc_1(X18)))&((~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X19=X20|~m1_subset_1(X20,k1_zfmisc_1(X18))|~m1_subset_1(X19,k1_zfmisc_1(X18)))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X19=X20|~m1_subset_1(X20,k1_zfmisc_1(X18))|~m1_subset_1(X19,k1_zfmisc_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.19/0.50  fof(c_0_42, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.50  cnf(c_0_43, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,a_2_1_orders_2(X1,X3))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.50  cnf(c_0_44, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.50  fof(c_0_45, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k2_orders_2(X1,k1_struct_0(X1))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t45_orders_2])).
% 0.19/0.50  fof(c_0_46, plain, ![X32]:(~l1_struct_0(X32)|k1_struct_0(X32)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).
% 0.19/0.50  fof(c_0_47, plain, ![X37]:(~l1_orders_2(X37)|l1_struct_0(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.50  cnf(c_0_48, plain, (v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_xboole_0(u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_40]), c_0_36])])).
% 0.19/0.50  cnf(c_0_49, plain, (m1_subset_1(esk2_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.50  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.50  cnf(c_0_51, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_36])])).
% 0.19/0.50  cnf(c_0_52, plain, (v2_struct_0(X1)|m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k2_orders_2(X1,X3))), inference(spm,[status(thm)],[c_0_44, c_0_19])).
% 0.19/0.50  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.50  fof(c_0_54, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&k2_orders_2(esk5_0,k1_struct_0(esk5_0))!=u1_struct_0(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_45])])])])).
% 0.19/0.50  cnf(c_0_55, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.50  cnf(c_0_56, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.50  cnf(c_0_57, plain, (X1=X2|v2_struct_0(X3)|~l1_orders_2(X3)|~v5_orders_2(X3)|~v4_orders_2(X3)|~v3_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))|~v1_xboole_0(u1_struct_0(X3))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.50  fof(c_0_58, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.50  cnf(c_0_59, plain, (v2_struct_0(X1)|r1_tarski(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk1_2(X2,u1_struct_0(X1)),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.50  cnf(c_0_60, plain, (v2_struct_0(X1)|m1_subset_1(esk1_2(k2_orders_2(X1,X2),X3),u1_struct_0(X1))|r1_tarski(k2_orders_2(X1,X2),X3)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.50  cnf(c_0_61, negated_conjecture, (k2_orders_2(esk5_0,k1_struct_0(esk5_0))!=u1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_62, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.50  cnf(c_0_63, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_64, plain, (X1=k2_orders_2(X2,X3)|v2_struct_0(X2)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v1_xboole_0(u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_57, c_0_19])).
% 0.19/0.50  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.50  cnf(c_0_66, plain, (v2_struct_0(X1)|r1_tarski(k2_orders_2(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.50  cnf(c_0_67, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.50  cnf(c_0_68, negated_conjecture, (k2_orders_2(esk5_0,k1_xboole_0)!=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 0.19/0.50  cnf(c_0_69, plain, (k2_orders_2(X1,X2)=k2_orders_2(X1,X3)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_64, c_0_19])).
% 0.19/0.50  cnf(c_0_70, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_71, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_72, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_73, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_74, plain, (k2_orders_2(X1,X2)=u1_struct_0(X1)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(u1_struct_0(X1),k2_orders_2(X1,X2))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.50  cnf(c_0_75, plain, (v2_struct_0(X1)|r1_tarski(X2,a_2_1_orders_2(X1,k1_xboole_0))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(esk1_2(X2,a_2_1_orders_2(X1,k1_xboole_0)),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_50, c_0_40])).
% 0.19/0.50  cnf(c_0_76, plain, (m1_subset_1(esk1_2(X1,X2),X1)|v1_xboole_0(X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_67, c_0_53])).
% 0.19/0.50  cnf(c_0_77, negated_conjecture, (k2_orders_2(esk5_0,X1)!=u1_struct_0(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_63]), c_0_70]), c_0_71]), c_0_72]), c_0_36])]), c_0_73])).
% 0.19/0.50  cnf(c_0_78, plain, (a_2_1_orders_2(X1,X2)=u1_struct_0(X1)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(u1_struct_0(X1),a_2_1_orders_2(X1,X2))), inference(spm,[status(thm)],[c_0_74, c_0_26])).
% 0.19/0.50  cnf(c_0_79, plain, (v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|r1_tarski(u1_struct_0(X1),a_2_1_orders_2(X1,k1_xboole_0))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.50  cnf(c_0_80, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.50  cnf(c_0_81, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.50  cnf(c_0_82, negated_conjecture, (a_2_1_orders_2(esk5_0,X1)!=u1_struct_0(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_26]), c_0_63]), c_0_70]), c_0_71]), c_0_72])]), c_0_73])).
% 0.19/0.50  cnf(c_0_83, plain, (a_2_1_orders_2(X1,k1_xboole_0)=u1_struct_0(X1)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_36])])).
% 0.19/0.50  cnf(c_0_84, negated_conjecture, (a_2_1_orders_2(esk5_0,k1_xboole_0)!=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_26]), c_0_63]), c_0_70]), c_0_71]), c_0_72]), c_0_36])]), c_0_73])).
% 0.19/0.50  cnf(c_0_85, plain, (m1_subset_1(X1,k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.50  cnf(c_0_86, negated_conjecture, (a_2_1_orders_2(esk5_0,X1)!=u1_struct_0(esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_63]), c_0_70]), c_0_71]), c_0_72])]), c_0_84]), c_0_73])).
% 0.19/0.50  cnf(c_0_87, plain, (a_2_1_orders_2(X1,k1_xboole_0)=u1_struct_0(X1)|v2_struct_0(X1)|m1_subset_1(u1_struct_0(X1),k1_xboole_0)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_85, c_0_83])).
% 0.19/0.50  cnf(c_0_88, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.50  cnf(c_0_89, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_36]), c_0_63]), c_0_70]), c_0_71]), c_0_72])]), c_0_73])).
% 0.19/0.50  cnf(c_0_90, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_81])])).
% 0.19/0.50  cnf(c_0_91, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk5_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_80, c_0_90])).
% 0.19/0.50  cnf(c_0_92, negated_conjecture, (m1_subset_1(k1_xboole_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_91, c_0_81])).
% 0.19/0.50  cnf(c_0_93, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_92]), c_0_63]), c_0_70]), c_0_71]), c_0_72]), c_0_90])]), c_0_73]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 94
% 0.19/0.50  # Proof object clause steps            : 62
% 0.19/0.50  # Proof object formula steps           : 32
% 0.19/0.50  # Proof object conjectures             : 19
% 0.19/0.50  # Proof object clause conjectures      : 16
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 27
% 0.19/0.50  # Proof object initial formulas used   : 16
% 0.19/0.50  # Proof object generating inferences   : 34
% 0.19/0.50  # Proof object simplifying inferences  : 55
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 17
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 36
% 0.19/0.50  # Removed in clause preprocessing      : 0
% 0.19/0.50  # Initial clauses in saturation        : 36
% 0.19/0.50  # Processed clauses                    : 1058
% 0.19/0.50  # ...of these trivial                  : 1
% 0.19/0.50  # ...subsumed                          : 760
% 0.19/0.50  # ...remaining for further processing  : 297
% 0.19/0.50  # Other redundant clauses eliminated   : 5
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 16
% 0.19/0.50  # Backward-rewritten                   : 5
% 0.19/0.50  # Generated clauses                    : 4451
% 0.19/0.50  # ...of the previous two non-trivial   : 4151
% 0.19/0.50  # Contextual simplify-reflections      : 10
% 0.19/0.50  # Paramodulations                      : 4416
% 0.19/0.50  # Factorizations                       : 30
% 0.19/0.50  # Equation resolutions                 : 5
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 271
% 0.19/0.50  #    Positive orientable unit clauses  : 12
% 0.19/0.50  #    Positive unorientable unit clauses: 0
% 0.19/0.50  #    Negative unit clauses             : 7
% 0.19/0.50  #    Non-unit-clauses                  : 252
% 0.19/0.50  # Current number of unprocessed clauses: 3101
% 0.19/0.50  # ...number of literals in the above   : 26117
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 21
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 21874
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 2814
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 708
% 0.19/0.50  # Unit Clause-clause subsumption calls : 162
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 3
% 0.19/0.50  # BW rewrite match successes           : 1
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 110628
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.158 s
% 0.19/0.50  # System time              : 0.006 s
% 0.19/0.50  # Total time               : 0.164 s
% 0.19/0.50  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
