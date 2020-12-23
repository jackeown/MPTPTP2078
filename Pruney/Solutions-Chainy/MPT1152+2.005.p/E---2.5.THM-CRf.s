%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:38 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 165 expanded)
%              Number of clauses        :   45 (  70 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  385 ( 943 expanded)
%              Number of equality atoms :   55 ( 133 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   56 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t46_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k2_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

fof(t49_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => r2_hidden(X3,X2) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(dt_k2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(c_0_14,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_16,plain,(
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

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_21,plain,(
    ! [X30,X31,X32] :
      ( ( r1_orders_2(X30,X31,X32)
        | ~ r2_orders_2(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( X31 != X32
        | ~ r2_orders_2(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( ~ r1_orders_2(X30,X31,X32)
        | X31 = X32
        | r2_orders_2(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_22,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | m1_subset_1(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_23,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk4_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k2_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t46_orders_2])).

cnf(c_0_27,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_orders_2(X2,esk3_3(X4,X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X12,X13] :
      ( ( m1_subset_1(esk1_2(X12,X13),X12)
        | X12 = X13
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | X12 = X13
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_1_orders_2(X1,k1_xboole_0))
    | X3 != k1_xboole_0
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

fof(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & k2_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])).

fof(c_0_33,plain,(
    ! [X28] :
      ( ~ l1_struct_0(X28)
      | k2_struct_0(X28) = u1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_34,plain,(
    ! [X29] :
      ( ~ l1_struct_0(X29)
      | m1_subset_1(k2_struct_0(X29),k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_35,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | r2_orders_2(X1,esk3_3(X2,X1,X3),X4)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_1_orders_2(X1,k1_xboole_0))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v3_orders_2(X35)
      | ~ v4_orders_2(X35)
      | ~ v5_orders_2(X35)
      | ~ l1_orders_2(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | m1_subset_1(k2_orders_2(X35,X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).

fof(c_0_40,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ v3_orders_2(X33)
      | ~ v4_orders_2(X33)
      | ~ v5_orders_2(X33)
      | ~ l1_orders_2(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | k2_orders_2(X33,X34) = a_2_1_orders_2(X33,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

cnf(c_0_41,negated_conjecture,
    ( k2_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_44,plain,(
    ! [X37] :
      ( ~ l1_orders_2(X37)
      | l1_struct_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(esk3_3(X3,X1,X2),X2)
    | ~ r2_hidden(X3,a_2_1_orders_2(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_29])).

cnf(c_0_46,plain,
    ( X1 = a_2_1_orders_2(X2,k1_xboole_0)
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(esk1_2(X1,a_2_1_orders_2(X2,k1_xboole_0)),u1_struct_0(X2))
    | ~ m1_subset_1(a_2_1_orders_2(X2,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( k2_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0
    | ~ l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_53,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_56,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_57,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk3_3(X3,X2,a_2_1_orders_2(X1,k1_xboole_0)),u1_struct_0(X1))
    | ~ m1_subset_1(a_2_1_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,a_2_1_orders_2(X2,a_2_1_orders_2(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_38])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,plain,
    ( a_2_1_orders_2(X1,k1_xboole_0) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(a_2_1_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(a_2_1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( a_2_1_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0
    | ~ l1_struct_0(esk5_0)
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_49]),c_0_51]),c_0_52]),c_0_53]),c_0_54])]),c_0_55])).

cnf(c_0_63,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(a_2_1_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,a_2_1_orders_2(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( a_2_1_orders_2(X1,k1_xboole_0) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_25])])).

fof(c_0_66,plain,(
    ! [X23,X25,X26,X27] :
      ( ( r2_hidden(esk2_1(X23),X23)
        | X23 = k1_xboole_0 )
      & ( ~ r2_hidden(X25,X23)
        | esk2_1(X23) != k3_mcart_1(X25,X26,X27)
        | X23 = k1_xboole_0 )
      & ( ~ r2_hidden(X26,X23)
        | esk2_1(X23) != k3_mcart_1(X25,X26,X27)
        | X23 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_67,negated_conjecture,
    ( a_2_1_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_57]),c_0_54])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_54])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_63])).

cnf(c_0_70,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( a_2_1_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_72,plain,
    ( a_2_1_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_51]),c_0_52]),c_0_53]),c_0_54])]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:18:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.33  # Version: 2.5pre002
% 0.18/0.34  # No SInE strategy applied
% 0.18/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.43  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.18/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.43  #
% 0.18/0.43  # Preprocessing time       : 0.045 s
% 0.18/0.43  # Presaturation interreduction done
% 0.18/0.43  
% 0.18/0.43  # Proof found!
% 0.18/0.43  # SZS status Theorem
% 0.18/0.43  # SZS output start CNFRefutation
% 0.18/0.43  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.18/0.43  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.43  fof(fraenkel_a_2_1_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_1_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 0.18/0.43  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.18/0.43  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 0.18/0.43  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.18/0.43  fof(t46_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k2_orders_2(X1,k2_struct_0(X1))=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 0.18/0.43  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 0.18/0.43  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.18/0.43  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.18/0.43  fof(dt_k2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 0.18/0.43  fof(d13_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 0.18/0.43  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.18/0.43  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.18/0.43  fof(c_0_14, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.18/0.43  fof(c_0_15, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.43  fof(c_0_16, plain, ![X38, X39, X40, X42, X43]:((((m1_subset_1(esk3_3(X38,X39,X40),u1_struct_0(X39))|~r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))))&(X38=esk3_3(X38,X39,X40)|~r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))))))&(~m1_subset_1(X42,u1_struct_0(X39))|(~r2_hidden(X42,X40)|r2_orders_2(X39,esk3_3(X38,X39,X40),X42))|~r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))))))&((m1_subset_1(esk4_4(X38,X39,X40,X43),u1_struct_0(X39))|(~m1_subset_1(X43,u1_struct_0(X39))|X38!=X43)|r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))))&((r2_hidden(esk4_4(X38,X39,X40,X43),X40)|(~m1_subset_1(X43,u1_struct_0(X39))|X38!=X43)|r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))))&(~r2_orders_2(X39,X43,esk4_4(X38,X39,X40,X43))|(~m1_subset_1(X43,u1_struct_0(X39))|X38!=X43)|r2_hidden(X38,a_2_1_orders_2(X39,X40))|(v2_struct_0(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~l1_orders_2(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).
% 0.18/0.43  cnf(c_0_17, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.43  cnf(c_0_18, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.43  cnf(c_0_19, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_1_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.43  fof(c_0_20, plain, ![X15]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.18/0.43  fof(c_0_21, plain, ![X30, X31, X32]:(((r1_orders_2(X30,X31,X32)|~r2_orders_2(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~m1_subset_1(X31,u1_struct_0(X30))|~l1_orders_2(X30))&(X31!=X32|~r2_orders_2(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~m1_subset_1(X31,u1_struct_0(X30))|~l1_orders_2(X30)))&(~r1_orders_2(X30,X31,X32)|X31=X32|r2_orders_2(X30,X31,X32)|~m1_subset_1(X32,u1_struct_0(X30))|~m1_subset_1(X31,u1_struct_0(X30))|~l1_orders_2(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.18/0.43  fof(c_0_22, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|m1_subset_1(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.18/0.43  cnf(c_0_23, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.43  cnf(c_0_24, plain, (v2_struct_0(X1)|r2_hidden(esk4_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_19])).
% 0.18/0.43  cnf(c_0_25, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.43  fof(c_0_26, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k2_orders_2(X1,k2_struct_0(X1))=k1_xboole_0)), inference(assume_negation,[status(cth)],[t46_orders_2])).
% 0.18/0.43  cnf(c_0_27, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.43  cnf(c_0_28, plain, (r2_orders_2(X2,esk3_3(X4,X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.43  cnf(c_0_29, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.43  fof(c_0_30, plain, ![X12, X13]:((m1_subset_1(esk1_2(X12,X13),X12)|X12=X13|~m1_subset_1(X13,k1_zfmisc_1(X12)))&(~r2_hidden(esk1_2(X12,X13),X13)|X12=X13|~m1_subset_1(X13,k1_zfmisc_1(X12)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.18/0.43  cnf(c_0_31, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_1_orders_2(X1,k1_xboole_0))|X3!=k1_xboole_0|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.18/0.43  fof(c_0_32, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&k2_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])).
% 0.18/0.43  fof(c_0_33, plain, ![X28]:(~l1_struct_0(X28)|k2_struct_0(X28)=u1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.18/0.43  fof(c_0_34, plain, ![X29]:(~l1_struct_0(X29)|m1_subset_1(k2_struct_0(X29),k1_zfmisc_1(u1_struct_0(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.18/0.43  cnf(c_0_35, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_27])).
% 0.18/0.43  cnf(c_0_36, plain, (v2_struct_0(X1)|r2_orders_2(X1,esk3_3(X2,X1,X3),X4)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,a_2_1_orders_2(X1,X3))|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.43  cnf(c_0_37, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.43  cnf(c_0_38, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_1_orders_2(X1,k1_xboole_0))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_31])).
% 0.18/0.43  fof(c_0_39, plain, ![X35, X36]:(v2_struct_0(X35)|~v3_orders_2(X35)|~v4_orders_2(X35)|~v5_orders_2(X35)|~l1_orders_2(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|m1_subset_1(k2_orders_2(X35,X36),k1_zfmisc_1(u1_struct_0(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).
% 0.18/0.43  fof(c_0_40, plain, ![X33, X34]:(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|k2_orders_2(X33,X34)=a_2_1_orders_2(X33,X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).
% 0.18/0.43  cnf(c_0_41, negated_conjecture, (k2_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.43  cnf(c_0_42, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.43  cnf(c_0_43, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.43  fof(c_0_44, plain, ![X37]:(~l1_orders_2(X37)|l1_struct_0(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.18/0.43  cnf(c_0_45, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(esk3_3(X3,X1,X2),X2)|~r2_hidden(X3,a_2_1_orders_2(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_29])).
% 0.18/0.43  cnf(c_0_46, plain, (X1=a_2_1_orders_2(X2,k1_xboole_0)|v2_struct_0(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(esk1_2(X1,a_2_1_orders_2(X2,k1_xboole_0)),u1_struct_0(X2))|~m1_subset_1(a_2_1_orders_2(X2,k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.43  cnf(c_0_47, plain, (m1_subset_1(esk1_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.43  cnf(c_0_48, plain, (v2_struct_0(X1)|m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.43  cnf(c_0_49, plain, (v2_struct_0(X1)|k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.43  cnf(c_0_50, negated_conjecture, (k2_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0|~l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.43  cnf(c_0_51, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.43  cnf(c_0_52, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.43  cnf(c_0_53, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.43  cnf(c_0_54, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.43  cnf(c_0_55, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.43  cnf(c_0_56, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.18/0.43  cnf(c_0_57, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.43  cnf(c_0_58, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v5_orders_2(X2)|~v5_orders_2(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v3_orders_2(X2)|~v3_orders_2(X1)|~l1_orders_2(X2)|~l1_orders_2(X1)|~m1_subset_1(esk3_3(X3,X2,a_2_1_orders_2(X1,k1_xboole_0)),u1_struct_0(X1))|~m1_subset_1(a_2_1_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,a_2_1_orders_2(X2,a_2_1_orders_2(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_45, c_0_38])).
% 0.18/0.43  cnf(c_0_59, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.43  cnf(c_0_60, plain, (a_2_1_orders_2(X1,k1_xboole_0)=u1_struct_0(X1)|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(a_2_1_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.43  cnf(c_0_61, plain, (v2_struct_0(X1)|m1_subset_1(a_2_1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.18/0.43  cnf(c_0_62, negated_conjecture, (a_2_1_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0|~l1_struct_0(esk5_0)|~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_49]), c_0_51]), c_0_52]), c_0_53]), c_0_54])]), c_0_55])).
% 0.18/0.43  cnf(c_0_63, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.43  cnf(c_0_64, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(a_2_1_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,a_2_1_orders_2(X1,a_2_1_orders_2(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.43  cnf(c_0_65, plain, (a_2_1_orders_2(X1,k1_xboole_0)=u1_struct_0(X1)|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_25])])).
% 0.18/0.43  fof(c_0_66, plain, ![X23, X25, X26, X27]:((r2_hidden(esk2_1(X23),X23)|X23=k1_xboole_0)&((~r2_hidden(X25,X23)|esk2_1(X23)!=k3_mcart_1(X25,X26,X27)|X23=k1_xboole_0)&(~r2_hidden(X26,X23)|esk2_1(X23)!=k3_mcart_1(X25,X26,X27)|X23=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.18/0.43  cnf(c_0_67, negated_conjecture, (a_2_1_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0|~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_57]), c_0_54])])).
% 0.18/0.43  cnf(c_0_68, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_63, c_0_54])).
% 0.18/0.43  cnf(c_0_69, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X2,a_2_1_orders_2(X1,u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_63])).
% 0.18/0.43  cnf(c_0_70, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.18/0.43  cnf(c_0_71, negated_conjecture, (a_2_1_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])])).
% 0.18/0.43  cnf(c_0_72, plain, (a_2_1_orders_2(X1,u1_struct_0(X1))=k1_xboole_0|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.18/0.43  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_51]), c_0_52]), c_0_53]), c_0_54])]), c_0_55]), ['proof']).
% 0.18/0.43  # SZS output end CNFRefutation
% 0.18/0.43  # Proof object total steps             : 74
% 0.18/0.43  # Proof object clause steps            : 45
% 0.18/0.43  # Proof object formula steps           : 29
% 0.18/0.43  # Proof object conjectures             : 15
% 0.18/0.43  # Proof object clause conjectures      : 12
% 0.18/0.43  # Proof object formula conjectures     : 3
% 0.18/0.43  # Proof object initial clauses used    : 22
% 0.18/0.43  # Proof object initial formulas used   : 14
% 0.18/0.43  # Proof object generating inferences   : 19
% 0.18/0.43  # Proof object simplifying inferences  : 25
% 0.18/0.43  # Training examples: 0 positive, 0 negative
% 0.18/0.43  # Parsed axioms                        : 17
% 0.18/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.43  # Initial clauses                      : 37
% 0.18/0.43  # Removed in clause preprocessing      : 0
% 0.18/0.43  # Initial clauses in saturation        : 37
% 0.18/0.43  # Processed clauses                    : 276
% 0.18/0.43  # ...of these trivial                  : 0
% 0.18/0.43  # ...subsumed                          : 72
% 0.18/0.43  # ...remaining for further processing  : 204
% 0.18/0.43  # Other redundant clauses eliminated   : 4
% 0.18/0.43  # Clauses deleted for lack of memory   : 0
% 0.18/0.43  # Backward-subsumed                    : 6
% 0.18/0.43  # Backward-rewritten                   : 1
% 0.18/0.43  # Generated clauses                    : 559
% 0.18/0.43  # ...of the previous two non-trivial   : 528
% 0.18/0.43  # Contextual simplify-reflections      : 12
% 0.18/0.43  # Paramodulations                      : 550
% 0.18/0.43  # Factorizations                       : 2
% 0.18/0.43  # Equation resolutions                 : 7
% 0.18/0.43  # Propositional unsat checks           : 0
% 0.18/0.43  #    Propositional check models        : 0
% 0.18/0.43  #    Propositional check unsatisfiable : 0
% 0.18/0.43  #    Propositional clauses             : 0
% 0.18/0.43  #    Propositional clauses after purity: 0
% 0.18/0.43  #    Propositional unsat core size     : 0
% 0.18/0.43  #    Propositional preprocessing time  : 0.000
% 0.18/0.43  #    Propositional encoding time       : 0.000
% 0.18/0.43  #    Propositional solver time         : 0.000
% 0.18/0.43  #    Success case prop preproc time    : 0.000
% 0.18/0.43  #    Success case prop encoding time   : 0.000
% 0.18/0.43  #    Success case prop solver time     : 0.000
% 0.18/0.43  # Current number of processed clauses  : 158
% 0.18/0.43  #    Positive orientable unit clauses  : 6
% 0.18/0.43  #    Positive unorientable unit clauses: 0
% 0.18/0.43  #    Negative unit clauses             : 4
% 0.18/0.43  #    Non-unit-clauses                  : 148
% 0.18/0.43  # Current number of unprocessed clauses: 323
% 0.18/0.43  # ...number of literals in the above   : 2197
% 0.18/0.43  # Current number of archived formulas  : 0
% 0.18/0.43  # Current number of archived clauses   : 42
% 0.18/0.43  # Clause-clause subsumption calls (NU) : 12864
% 0.18/0.43  # Rec. Clause-clause subsumption calls : 3196
% 0.18/0.43  # Non-unit clause-clause subsumptions  : 90
% 0.18/0.43  # Unit Clause-clause subsumption calls : 18
% 0.18/0.43  # Rewrite failures with RHS unbound    : 0
% 0.18/0.43  # BW rewrite match attempts            : 1
% 0.18/0.43  # BW rewrite match successes           : 1
% 0.18/0.43  # Condensation attempts                : 0
% 0.18/0.43  # Condensation successes               : 0
% 0.18/0.43  # Termbank termtop insertions          : 16086
% 0.18/0.43  
% 0.18/0.43  # -------------------------------------------------
% 0.18/0.43  # User time                : 0.089 s
% 0.18/0.43  # System time              : 0.007 s
% 0.18/0.43  # Total time               : 0.096 s
% 0.18/0.43  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
