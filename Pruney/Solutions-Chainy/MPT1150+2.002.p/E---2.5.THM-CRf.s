%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:33 EST 2020

% Result     : Theorem 1.28s
% Output     : CNFRefutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 180 expanded)
%              Number of clauses        :   51 (  78 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  403 ( 978 expanded)
%              Number of equality atoms :   42 ( 108 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   56 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fraenkel_a_2_0_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X5,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k1_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(d12_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(t44_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | ~ r1_tarski(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_17,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_18,plain,(
    ! [X39,X40,X41,X43,X44] :
      ( ( m1_subset_1(esk3_3(X39,X40,X41),u1_struct_0(X40))
        | ~ r2_hidden(X39,a_2_0_orders_2(X40,X41))
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ l1_orders_2(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))) )
      & ( X39 = esk3_3(X39,X40,X41)
        | ~ r2_hidden(X39,a_2_0_orders_2(X40,X41))
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ l1_orders_2(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))) )
      & ( ~ m1_subset_1(X43,u1_struct_0(X40))
        | ~ r2_hidden(X43,X41)
        | r2_orders_2(X40,X43,esk3_3(X39,X40,X41))
        | ~ r2_hidden(X39,a_2_0_orders_2(X40,X41))
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ l1_orders_2(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))) )
      & ( m1_subset_1(esk4_4(X39,X40,X41,X44),u1_struct_0(X40))
        | ~ m1_subset_1(X44,u1_struct_0(X40))
        | X39 != X44
        | r2_hidden(X39,a_2_0_orders_2(X40,X41))
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ l1_orders_2(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))) )
      & ( r2_hidden(esk4_4(X39,X40,X41,X44),X41)
        | ~ m1_subset_1(X44,u1_struct_0(X40))
        | X39 != X44
        | r2_hidden(X39,a_2_0_orders_2(X40,X41))
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ l1_orders_2(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))) )
      & ( ~ r2_orders_2(X40,esk4_4(X39,X40,X41,X44),X44)
        | ~ m1_subset_1(X44,u1_struct_0(X40))
        | X39 != X44
        | r2_hidden(X39,a_2_0_orders_2(X40,X41))
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ l1_orders_2(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

fof(c_0_19,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X3)
    | r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | X1 != X4
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_25,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | m1_subset_1(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X31,X32,X33] :
      ( ( r1_orders_2(X31,X32,X33)
        | ~ r2_orders_2(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( X32 != X33
        | ~ r2_orders_2(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( ~ r1_orders_2(X31,X32,X33)
        | X32 = X33
        | r2_orders_2(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_29,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk4_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_orders_2(X2,X1,esk3_3(X4,X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_39,plain,(
    ! [X36,X37] :
      ( v2_struct_0(X36)
      | ~ v3_orders_2(X36)
      | ~ v4_orders_2(X36)
      | ~ v5_orders_2(X36)
      | ~ l1_orders_2(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | m1_subset_1(k1_orders_2(X36,X37),k1_zfmisc_1(u1_struct_0(X36))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).

fof(c_0_40,plain,(
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ v3_orders_2(X34)
      | ~ v4_orders_2(X34)
      | ~ v5_orders_2(X34)
      | ~ l1_orders_2(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | k1_orders_2(X34,X35) = a_2_0_orders_2(X34,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_0_orders_2(X1,k1_xboole_0))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_orders_2])).

cnf(c_0_46,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | r2_orders_2(X1,X2,esk3_3(X3,X1,X4))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X4))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[c_0_36,c_0_33])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X2,a_2_0_orders_2(X1,k1_xboole_0))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk1_2(X2,a_2_0_orders_2(X1,k1_xboole_0)),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & k1_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_45])])])])).

fof(c_0_54,plain,(
    ! [X30] :
      ( ~ l1_struct_0(X30)
      | k2_struct_0(X30) = u1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(esk3_3(X3,X1,X2),X2)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_33])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_38])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(a_2_0_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | r1_tarski(u1_struct_0(X1),a_2_0_orders_2(X1,k1_xboole_0))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k1_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
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
    | ~ m1_subset_1(esk3_3(X3,X2,a_2_0_orders_2(X1,k1_xboole_0)),u1_struct_0(X1))
    | ~ m1_subset_1(a_2_0_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,a_2_0_orders_2(X2,a_2_0_orders_2(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_42])).

cnf(c_0_62,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,plain,
    ( a_2_0_orders_2(X1,X2) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(a_2_0_orders_2(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(a_2_0_orders_2(X1,k1_xboole_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k1_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0
    | ~ l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_71,plain,(
    ! [X38] :
      ( ~ l1_orders_2(X38)
      | l1_struct_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(a_2_0_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,a_2_0_orders_2(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_73,plain,
    ( a_2_0_orders_2(X1,k1_xboole_0) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_32])])).

fof(c_0_74,plain,(
    ! [X24,X26,X27,X28,X29] :
      ( ( r2_hidden(esk2_1(X24),X24)
        | X24 = k1_xboole_0 )
      & ( ~ r2_hidden(X26,X24)
        | esk2_1(X24) != k4_mcart_1(X26,X27,X28,X29)
        | X24 = k1_xboole_0 )
      & ( ~ r2_hidden(X27,X24)
        | esk2_1(X24) != k4_mcart_1(X26,X27,X28,X29)
        | X24 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_75,negated_conjecture,
    ( a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_50]),c_0_66]),c_0_67]),c_0_68]),c_0_69]),c_0_34])]),c_0_70])).

cnf(c_0_76,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_34])])).

cnf(c_0_78,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_69])])).

cnf(c_0_80,plain,
    ( a_2_0_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_66]),c_0_67]),c_0_68]),c_0_69])]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.28/1.44  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 1.28/1.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.28/1.44  #
% 1.28/1.44  # Preprocessing time       : 0.029 s
% 1.28/1.44  
% 1.28/1.44  # Proof found!
% 1.28/1.44  # SZS status Theorem
% 1.28/1.44  # SZS output start CNFRefutation
% 1.28/1.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.28/1.44  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.28/1.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.28/1.44  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 1.28/1.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.28/1.44  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.28/1.44  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 1.28/1.44  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 1.28/1.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.28/1.44  fof(dt_k1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 1.28/1.44  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 1.28/1.44  fof(t44_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 1.28/1.44  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 1.28/1.44  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 1.28/1.44  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 1.28/1.44  fof(c_0_15, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.28/1.44  fof(c_0_16, plain, ![X22, X23]:(~r2_hidden(X22,X23)|~r1_tarski(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 1.28/1.44  fof(c_0_17, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.28/1.44  fof(c_0_18, plain, ![X39, X40, X41, X43, X44]:((((m1_subset_1(esk3_3(X39,X40,X41),u1_struct_0(X40))|~r2_hidden(X39,a_2_0_orders_2(X40,X41))|(v2_struct_0(X40)|~v3_orders_2(X40)|~v4_orders_2(X40)|~v5_orders_2(X40)|~l1_orders_2(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))))&(X39=esk3_3(X39,X40,X41)|~r2_hidden(X39,a_2_0_orders_2(X40,X41))|(v2_struct_0(X40)|~v3_orders_2(X40)|~v4_orders_2(X40)|~v5_orders_2(X40)|~l1_orders_2(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))))))&(~m1_subset_1(X43,u1_struct_0(X40))|(~r2_hidden(X43,X41)|r2_orders_2(X40,X43,esk3_3(X39,X40,X41)))|~r2_hidden(X39,a_2_0_orders_2(X40,X41))|(v2_struct_0(X40)|~v3_orders_2(X40)|~v4_orders_2(X40)|~v5_orders_2(X40)|~l1_orders_2(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40))))))&((m1_subset_1(esk4_4(X39,X40,X41,X44),u1_struct_0(X40))|(~m1_subset_1(X44,u1_struct_0(X40))|X39!=X44)|r2_hidden(X39,a_2_0_orders_2(X40,X41))|(v2_struct_0(X40)|~v3_orders_2(X40)|~v4_orders_2(X40)|~v5_orders_2(X40)|~l1_orders_2(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))))&((r2_hidden(esk4_4(X39,X40,X41,X44),X41)|(~m1_subset_1(X44,u1_struct_0(X40))|X39!=X44)|r2_hidden(X39,a_2_0_orders_2(X40,X41))|(v2_struct_0(X40)|~v3_orders_2(X40)|~v4_orders_2(X40)|~v5_orders_2(X40)|~l1_orders_2(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))))&(~r2_orders_2(X40,esk4_4(X39,X40,X41,X44),X44)|(~m1_subset_1(X44,u1_struct_0(X40))|X39!=X44)|r2_hidden(X39,a_2_0_orders_2(X40,X41))|(v2_struct_0(X40)|~v3_orders_2(X40)|~v4_orders_2(X40)|~v5_orders_2(X40)|~l1_orders_2(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 1.28/1.44  fof(c_0_19, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.28/1.44  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.28/1.44  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.28/1.44  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.28/1.44  cnf(c_0_23, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_0_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.28/1.44  fof(c_0_24, plain, ![X16]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 1.28/1.44  fof(c_0_25, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|m1_subset_1(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.28/1.44  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.28/1.44  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 1.28/1.44  fof(c_0_28, plain, ![X31, X32, X33]:(((r1_orders_2(X31,X32,X33)|~r2_orders_2(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31))&(X32!=X33|~r2_orders_2(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31)))&(~r1_orders_2(X31,X32,X33)|X32=X33|r2_orders_2(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|~l1_orders_2(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 1.28/1.44  fof(c_0_29, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.28/1.44  cnf(c_0_30, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.28/1.44  cnf(c_0_31, plain, (v2_struct_0(X1)|r2_hidden(esk4_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_0_orders_2(X1,X3))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_23])).
% 1.28/1.44  cnf(c_0_32, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.28/1.44  cnf(c_0_33, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.28/1.44  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.28/1.44  cnf(c_0_35, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.28/1.44  cnf(c_0_36, plain, (r2_orders_2(X2,X1,esk3_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.28/1.44  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.28/1.44  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.28/1.44  fof(c_0_39, plain, ![X36, X37]:(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|m1_subset_1(k1_orders_2(X36,X37),k1_zfmisc_1(u1_struct_0(X36)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).
% 1.28/1.44  fof(c_0_40, plain, ![X34, X35]:(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|k1_orders_2(X34,X35)=a_2_0_orders_2(X34,X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 1.28/1.44  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.28/1.44  cnf(c_0_42, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_0_orders_2(X1,k1_xboole_0))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 1.28/1.44  cnf(c_0_43, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.28/1.44  cnf(c_0_44, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.28/1.44  fof(c_0_45, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0)), inference(assume_negation,[status(cth)],[t44_orders_2])).
% 1.28/1.44  cnf(c_0_46, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_35])).
% 1.28/1.44  cnf(c_0_47, plain, (v2_struct_0(X1)|r2_orders_2(X1,X2,esk3_3(X3,X1,X4))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,a_2_0_orders_2(X1,X4))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[c_0_36, c_0_33])).
% 1.28/1.44  cnf(c_0_48, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.28/1.44  cnf(c_0_49, plain, (v2_struct_0(X1)|m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.28/1.44  cnf(c_0_50, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.28/1.44  cnf(c_0_51, plain, (v2_struct_0(X1)|r1_tarski(X2,a_2_0_orders_2(X1,k1_xboole_0))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(esk1_2(X2,a_2_0_orders_2(X1,k1_xboole_0)),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.28/1.44  cnf(c_0_52, plain, (m1_subset_1(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.28/1.44  fof(c_0_53, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&k1_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_45])])])])).
% 1.28/1.44  fof(c_0_54, plain, ![X30]:(~l1_struct_0(X30)|k2_struct_0(X30)=u1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 1.28/1.44  cnf(c_0_55, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(esk3_3(X3,X1,X2),X2)|~r2_hidden(X3,a_2_0_orders_2(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_33])).
% 1.28/1.44  cnf(c_0_56, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_48, c_0_38])).
% 1.28/1.44  cnf(c_0_57, plain, (v2_struct_0(X1)|m1_subset_1(a_2_0_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.28/1.44  cnf(c_0_58, plain, (v2_struct_0(X1)|r1_tarski(u1_struct_0(X1),a_2_0_orders_2(X1,k1_xboole_0))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.28/1.44  cnf(c_0_59, negated_conjecture, (k1_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.28/1.44  cnf(c_0_60, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.28/1.44  cnf(c_0_61, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v5_orders_2(X2)|~v5_orders_2(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v3_orders_2(X2)|~v3_orders_2(X1)|~l1_orders_2(X2)|~l1_orders_2(X1)|~m1_subset_1(esk3_3(X3,X2,a_2_0_orders_2(X1,k1_xboole_0)),u1_struct_0(X1))|~m1_subset_1(a_2_0_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,a_2_0_orders_2(X2,a_2_0_orders_2(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_55, c_0_42])).
% 1.28/1.44  cnf(c_0_62, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.28/1.44  cnf(c_0_63, plain, (a_2_0_orders_2(X1,X2)=u1_struct_0(X1)|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(a_2_0_orders_2(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.28/1.44  cnf(c_0_64, plain, (v2_struct_0(X1)|m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(a_2_0_orders_2(X1,k1_xboole_0)))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_58])).
% 1.28/1.44  cnf(c_0_65, negated_conjecture, (k1_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0|~l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.28/1.44  cnf(c_0_66, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.28/1.44  cnf(c_0_67, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.28/1.44  cnf(c_0_68, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.28/1.44  cnf(c_0_69, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.28/1.44  cnf(c_0_70, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.28/1.44  fof(c_0_71, plain, ![X38]:(~l1_orders_2(X38)|l1_struct_0(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 1.28/1.44  cnf(c_0_72, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(a_2_0_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,a_2_0_orders_2(X1,a_2_0_orders_2(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 1.28/1.44  cnf(c_0_73, plain, (a_2_0_orders_2(X1,k1_xboole_0)=u1_struct_0(X1)|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_32])])).
% 1.28/1.44  fof(c_0_74, plain, ![X24, X26, X27, X28, X29]:((r2_hidden(esk2_1(X24),X24)|X24=k1_xboole_0)&((~r2_hidden(X26,X24)|esk2_1(X24)!=k4_mcart_1(X26,X27,X28,X29)|X24=k1_xboole_0)&(~r2_hidden(X27,X24)|esk2_1(X24)!=k4_mcart_1(X26,X27,X28,X29)|X24=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 1.28/1.44  cnf(c_0_75, negated_conjecture, (a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_50]), c_0_66]), c_0_67]), c_0_68]), c_0_69]), c_0_34])]), c_0_70])).
% 1.28/1.44  cnf(c_0_76, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.28/1.44  cnf(c_0_77, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X2,a_2_0_orders_2(X1,u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_34])])).
% 1.28/1.44  cnf(c_0_78, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_74])).
% 1.28/1.44  cnf(c_0_79, negated_conjecture, (a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_69])])).
% 1.28/1.44  cnf(c_0_80, plain, (a_2_0_orders_2(X1,u1_struct_0(X1))=k1_xboole_0|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 1.28/1.44  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_66]), c_0_67]), c_0_68]), c_0_69])]), c_0_70]), ['proof']).
% 1.28/1.44  # SZS output end CNFRefutation
% 1.28/1.44  # Proof object total steps             : 82
% 1.28/1.44  # Proof object clause steps            : 51
% 1.28/1.44  # Proof object formula steps           : 31
% 1.28/1.44  # Proof object conjectures             : 13
% 1.28/1.44  # Proof object clause conjectures      : 10
% 1.28/1.44  # Proof object formula conjectures     : 3
% 1.28/1.44  # Proof object initial clauses used    : 25
% 1.28/1.44  # Proof object initial formulas used   : 15
% 1.28/1.44  # Proof object generating inferences   : 22
% 1.28/1.44  # Proof object simplifying inferences  : 26
% 1.28/1.44  # Training examples: 0 positive, 0 negative
% 1.28/1.44  # Parsed axioms                        : 15
% 1.28/1.44  # Removed by relevancy pruning/SinE    : 0
% 1.28/1.44  # Initial clauses                      : 34
% 1.28/1.44  # Removed in clause preprocessing      : 0
% 1.28/1.44  # Initial clauses in saturation        : 34
% 1.28/1.44  # Processed clauses                    : 11309
% 1.28/1.44  # ...of these trivial                  : 371
% 1.28/1.44  # ...subsumed                          : 9307
% 1.28/1.44  # ...remaining for further processing  : 1631
% 1.28/1.44  # Other redundant clauses eliminated   : 6
% 1.28/1.44  # Clauses deleted for lack of memory   : 0
% 1.28/1.44  # Backward-subsumed                    : 161
% 1.28/1.44  # Backward-rewritten                   : 0
% 1.28/1.44  # Generated clauses                    : 70424
% 1.28/1.44  # ...of the previous two non-trivial   : 63625
% 1.28/1.44  # Contextual simplify-reflections      : 44
% 1.28/1.44  # Paramodulations                      : 70397
% 1.28/1.44  # Factorizations                       : 21
% 1.28/1.44  # Equation resolutions                 : 6
% 1.28/1.44  # Propositional unsat checks           : 0
% 1.28/1.44  #    Propositional check models        : 0
% 1.28/1.44  #    Propositional check unsatisfiable : 0
% 1.28/1.44  #    Propositional clauses             : 0
% 1.28/1.44  #    Propositional clauses after purity: 0
% 1.28/1.44  #    Propositional unsat core size     : 0
% 1.28/1.44  #    Propositional preprocessing time  : 0.000
% 1.28/1.44  #    Propositional encoding time       : 0.000
% 1.28/1.44  #    Propositional solver time         : 0.000
% 1.28/1.44  #    Success case prop preproc time    : 0.000
% 1.28/1.44  #    Success case prop encoding time   : 0.000
% 1.28/1.44  #    Success case prop solver time     : 0.000
% 1.28/1.44  # Current number of processed clauses  : 1464
% 1.28/1.44  #    Positive orientable unit clauses  : 8
% 1.28/1.44  #    Positive unorientable unit clauses: 0
% 1.28/1.44  #    Negative unit clauses             : 5
% 1.28/1.44  #    Non-unit-clauses                  : 1451
% 1.28/1.44  # Current number of unprocessed clauses: 51620
% 1.28/1.44  # ...number of literals in the above   : 324912
% 1.28/1.44  # Current number of archived formulas  : 0
% 1.28/1.44  # Current number of archived clauses   : 161
% 1.28/1.44  # Clause-clause subsumption calls (NU) : 543898
% 1.28/1.44  # Rec. Clause-clause subsumption calls : 53921
% 1.28/1.44  # Non-unit clause-clause subsumptions  : 8648
% 1.28/1.44  # Unit Clause-clause subsumption calls : 6
% 1.28/1.44  # Rewrite failures with RHS unbound    : 0
% 1.28/1.44  # BW rewrite match attempts            : 4
% 1.28/1.44  # BW rewrite match successes           : 0
% 1.28/1.44  # Condensation attempts                : 0
% 1.28/1.44  # Condensation successes               : 0
% 1.28/1.44  # Termbank termtop insertions          : 1619902
% 1.28/1.45  
% 1.28/1.45  # -------------------------------------------------
% 1.28/1.45  # User time                : 1.074 s
% 1.28/1.45  # System time              : 0.030 s
% 1.28/1.45  # Total time               : 1.104 s
% 1.28/1.45  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
