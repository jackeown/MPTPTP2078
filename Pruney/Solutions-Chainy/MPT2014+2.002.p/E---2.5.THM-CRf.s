%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  62 expanded)
%              Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  321 ( 564 expanded)
%              Number of equality atoms :   27 (  49 expanded)
%              Maximal formula depth    :   30 (   7 average)
%              Maximal clause size      :  110 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( ( v6_waybel_0(X4,X1)
                    & l1_waybel_0(X4,X1) )
                 => ( X4 = k4_waybel_9(X1,X2,X3)
                  <=> ( ! [X5] :
                          ( r2_hidden(X5,u1_struct_0(X4))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                              & X6 = X5
                              & r1_orders_2(X2,X3,X6) ) )
                      & r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4)))
                      & u1_waybel_0(X1,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_k4_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
        & l1_waybel_0(k4_waybel_9(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(fc15_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & ~ v1_xboole_0(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc15_yellow_6)).

fof(t13_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

fof(c_0_8,plain,(
    ! [X22,X23,X24,X25,X26,X28,X29,X31] :
      ( ( m1_subset_1(esk2_5(X22,X23,X24,X25,X26),u1_struct_0(X23))
        | ~ r2_hidden(X26,u1_struct_0(X25))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( esk2_5(X22,X23,X24,X25,X26) = X26
        | ~ r2_hidden(X26,u1_struct_0(X25))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( r1_orders_2(X23,X24,esk2_5(X22,X23,X24,X25,X26))
        | ~ r2_hidden(X26,u1_struct_0(X25))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( ~ m1_subset_1(X29,u1_struct_0(X23))
        | X29 != X28
        | ~ r1_orders_2(X23,X24,X29)
        | r2_hidden(X28,u1_struct_0(X25))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( u1_waybel_0(X22,X25) = k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( ~ r2_hidden(esk3_4(X22,X23,X24,X25),u1_struct_0(X25))
        | ~ m1_subset_1(X31,u1_struct_0(X23))
        | X31 != esk3_4(X22,X23,X24,X25)
        | ~ r1_orders_2(X23,X24,X31)
        | ~ r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))
        | u1_waybel_0(X22,X25) != k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))
        | X25 = k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( m1_subset_1(esk4_4(X22,X23,X24,X25),u1_struct_0(X23))
        | r2_hidden(esk3_4(X22,X23,X24,X25),u1_struct_0(X25))
        | ~ r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))
        | u1_waybel_0(X22,X25) != k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))
        | X25 = k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( esk4_4(X22,X23,X24,X25) = esk3_4(X22,X23,X24,X25)
        | r2_hidden(esk3_4(X22,X23,X24,X25),u1_struct_0(X25))
        | ~ r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))
        | u1_waybel_0(X22,X25) != k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))
        | X25 = k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( r1_orders_2(X23,X24,esk4_4(X22,X23,X24,X25))
        | r2_hidden(esk3_4(X22,X23,X24,X25),u1_struct_0(X25))
        | ~ r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))
        | u1_waybel_0(X22,X25) != k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))
        | X25 = k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X1,X2,X3)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_10,plain,
    ( esk2_5(X1,X2,X3,X4,X5) = X5
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X1,X2,X3)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_xboole_0(X15)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v1_xboole_0(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

fof(c_0_13,plain,(
    ! [X18,X19] :
      ( ( v1_funct_1(u1_waybel_0(X18,X19))
        | ~ l1_struct_0(X18)
        | ~ l1_waybel_0(X19,X18) )
      & ( v1_funct_2(u1_waybel_0(X18,X19),u1_struct_0(X19),u1_struct_0(X18))
        | ~ l1_struct_0(X18)
        | ~ l1_waybel_0(X19,X18) )
      & ( m1_subset_1(u1_waybel_0(X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X18))))
        | ~ l1_struct_0(X18)
        | ~ l1_waybel_0(X19,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

fof(c_0_14,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X13,X14)
      | v1_xboole_0(X14)
      | r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X2))
    | X4 != k4_waybel_9(X1,X2,X5)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ r2_hidden(X3,u1_struct_0(X4)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X33,X34,X35] :
      ( ( v6_waybel_0(k4_waybel_9(X33,X34,X35),X33)
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33)
        | v2_struct_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | ~ m1_subset_1(X35,u1_struct_0(X34)) )
      & ( l1_waybel_0(k4_waybel_9(X33,X34,X35),X33)
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33)
        | v2_struct_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | ~ m1_subset_1(X35,u1_struct_0(X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).

fof(c_0_18,plain,(
    ! [X20,X21] :
      ( ( v1_funct_1(u1_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20) )
      & ( ~ v1_xboole_0(u1_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20) )
      & ( v1_funct_2(u1_waybel_0(X20,X21),u1_struct_0(X21),u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc15_yellow_6])])])])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_waybel_9])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk1_2(u1_struct_0(X3),X4),u1_struct_0(X1))
    | r1_tarski(u1_struct_0(X3),X4)
    | X3 != k4_waybel_9(X2,X1,X5)
    | ~ v6_waybel_0(X3,X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_xboole_0(u1_waybel_0(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( v1_xboole_0(u1_waybel_0(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_struct_0(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & l1_waybel_0(esk6_0,esk5_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & ~ r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X1)
    | ~ m1_subset_1(esk1_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk1_2(u1_struct_0(k4_waybel_9(X1,X2,X3)),X4),u1_struct_0(X2))
    | r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_tarski(u1_struct_0(k4_waybel_9(X2,X1,X3)),u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.029 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(d7_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>![X4]:((v6_waybel_0(X4,X1)&l1_waybel_0(X4,X1))=>(X4=k4_waybel_9(X1,X2,X3)<=>((![X5]:(r2_hidden(X5,u1_struct_0(X4))<=>?[X6]:((m1_subset_1(X6,u1_struct_0(X2))&X6=X5)&r1_orders_2(X2,X3,X6)))&r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4))))&u1_waybel_0(X1,X4)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_waybel_9)).
% 0.19/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.39  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.19/0.39  fof(dt_u1_waybel_0, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>((v1_funct_1(u1_waybel_0(X1,X2))&v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 0.19/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.39  fof(dt_k4_waybel_9, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))&m1_subset_1(X3,u1_struct_0(X2)))=>(v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)&l1_waybel_0(k4_waybel_9(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 0.19/0.39  fof(fc15_yellow_6, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))=>((v1_funct_1(u1_waybel_0(X1,X2))&~(v1_xboole_0(u1_waybel_0(X1,X2))))&v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc15_yellow_6)).
% 0.19/0.39  fof(t13_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_waybel_9)).
% 0.19/0.39  fof(c_0_8, plain, ![X22, X23, X24, X25, X26, X28, X29, X31]:(((((((m1_subset_1(esk2_5(X22,X23,X24,X25,X26),u1_struct_0(X23))|~r2_hidden(X26,u1_struct_0(X25))|X25!=k4_waybel_9(X22,X23,X24)|(~v6_waybel_0(X25,X22)|~l1_waybel_0(X25,X22))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22)))&(esk2_5(X22,X23,X24,X25,X26)=X26|~r2_hidden(X26,u1_struct_0(X25))|X25!=k4_waybel_9(X22,X23,X24)|(~v6_waybel_0(X25,X22)|~l1_waybel_0(X25,X22))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22))))&(r1_orders_2(X23,X24,esk2_5(X22,X23,X24,X25,X26))|~r2_hidden(X26,u1_struct_0(X25))|X25!=k4_waybel_9(X22,X23,X24)|(~v6_waybel_0(X25,X22)|~l1_waybel_0(X25,X22))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22))))&(~m1_subset_1(X29,u1_struct_0(X23))|X29!=X28|~r1_orders_2(X23,X24,X29)|r2_hidden(X28,u1_struct_0(X25))|X25!=k4_waybel_9(X22,X23,X24)|(~v6_waybel_0(X25,X22)|~l1_waybel_0(X25,X22))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22))))&(r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))|X25!=k4_waybel_9(X22,X23,X24)|(~v6_waybel_0(X25,X22)|~l1_waybel_0(X25,X22))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22))))&(u1_waybel_0(X22,X25)=k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))|X25!=k4_waybel_9(X22,X23,X24)|(~v6_waybel_0(X25,X22)|~l1_waybel_0(X25,X22))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22))))&((~r2_hidden(esk3_4(X22,X23,X24,X25),u1_struct_0(X25))|(~m1_subset_1(X31,u1_struct_0(X23))|X31!=esk3_4(X22,X23,X24,X25)|~r1_orders_2(X23,X24,X31))|~r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))|u1_waybel_0(X22,X25)!=k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))|X25=k4_waybel_9(X22,X23,X24)|(~v6_waybel_0(X25,X22)|~l1_waybel_0(X25,X22))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22)))&(((m1_subset_1(esk4_4(X22,X23,X24,X25),u1_struct_0(X23))|r2_hidden(esk3_4(X22,X23,X24,X25),u1_struct_0(X25))|~r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))|u1_waybel_0(X22,X25)!=k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))|X25=k4_waybel_9(X22,X23,X24)|(~v6_waybel_0(X25,X22)|~l1_waybel_0(X25,X22))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22)))&(esk4_4(X22,X23,X24,X25)=esk3_4(X22,X23,X24,X25)|r2_hidden(esk3_4(X22,X23,X24,X25),u1_struct_0(X25))|~r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))|u1_waybel_0(X22,X25)!=k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))|X25=k4_waybel_9(X22,X23,X24)|(~v6_waybel_0(X25,X22)|~l1_waybel_0(X25,X22))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22))))&(r1_orders_2(X23,X24,esk4_4(X22,X23,X24,X25))|r2_hidden(esk3_4(X22,X23,X24,X25),u1_struct_0(X25))|~r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))|u1_waybel_0(X22,X25)!=k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))|X25=k4_waybel_9(X22,X23,X24)|(~v6_waybel_0(X25,X22)|~l1_waybel_0(X25,X22))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).
% 0.19/0.39  cnf(c_0_9, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X1,X2,X3)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_10, plain, (esk2_5(X1,X2,X3,X4,X5)=X5|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(X5,u1_struct_0(X4))|X4!=k4_waybel_9(X1,X2,X3)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  fof(c_0_11, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.39  fof(c_0_12, plain, ![X15, X16, X17]:(~v1_xboole_0(X15)|(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|v1_xboole_0(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.19/0.39  fof(c_0_13, plain, ![X18, X19]:(((v1_funct_1(u1_waybel_0(X18,X19))|(~l1_struct_0(X18)|~l1_waybel_0(X19,X18)))&(v1_funct_2(u1_waybel_0(X18,X19),u1_struct_0(X19),u1_struct_0(X18))|(~l1_struct_0(X18)|~l1_waybel_0(X19,X18))))&(m1_subset_1(u1_waybel_0(X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X18))))|(~l1_struct_0(X18)|~l1_waybel_0(X19,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).
% 0.19/0.39  fof(c_0_14, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.39  cnf(c_0_15, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X2))|X4!=k4_waybel_9(X1,X2,X5)|~v6_waybel_0(X4,X1)|~l1_waybel_0(X4,X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X5,u1_struct_0(X2))|~r2_hidden(X3,u1_struct_0(X4))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.39  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  fof(c_0_17, plain, ![X33, X34, X35]:((v6_waybel_0(k4_waybel_9(X33,X34,X35),X33)|(v2_struct_0(X33)|~l1_struct_0(X33)|v2_struct_0(X34)|~l1_waybel_0(X34,X33)|~m1_subset_1(X35,u1_struct_0(X34))))&(l1_waybel_0(k4_waybel_9(X33,X34,X35),X33)|(v2_struct_0(X33)|~l1_struct_0(X33)|v2_struct_0(X34)|~l1_waybel_0(X34,X33)|~m1_subset_1(X35,u1_struct_0(X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).
% 0.19/0.39  fof(c_0_18, plain, ![X20, X21]:(((v1_funct_1(u1_waybel_0(X20,X21))|(v2_struct_0(X20)|~l1_struct_0(X20)|v2_struct_0(X21)|~l1_waybel_0(X21,X20)))&(~v1_xboole_0(u1_waybel_0(X20,X21))|(v2_struct_0(X20)|~l1_struct_0(X20)|v2_struct_0(X21)|~l1_waybel_0(X21,X20))))&(v1_funct_2(u1_waybel_0(X20,X21),u1_struct_0(X21),u1_struct_0(X20))|(v2_struct_0(X20)|~l1_struct_0(X20)|v2_struct_0(X21)|~l1_waybel_0(X21,X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc15_yellow_6])])])])).
% 0.19/0.39  cnf(c_0_19, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_20, plain, (m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  fof(c_0_21, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)))))), inference(assume_negation,[status(cth)],[t13_waybel_9])).
% 0.19/0.39  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_23, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_24, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk1_2(u1_struct_0(X3),X4),u1_struct_0(X1))|r1_tarski(u1_struct_0(X3),X4)|X3!=k4_waybel_9(X2,X1,X5)|~v6_waybel_0(X3,X2)|~l1_waybel_0(X3,X2)|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X5,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.39  cnf(c_0_25, plain, (l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_26, plain, (v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_27, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v1_xboole_0(u1_waybel_0(X1,X2))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_28, plain, (v1_xboole_0(u1_waybel_0(X1,X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.39  fof(c_0_29, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_struct_0(esk5_0))&((~v2_struct_0(esk6_0)&l1_waybel_0(esk6_0,esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&~r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.19/0.39  cnf(c_0_30, plain, (v1_xboole_0(X1)|r1_tarski(X2,X1)|~m1_subset_1(esk1_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.39  cnf(c_0_31, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk1_2(u1_struct_0(k4_waybel_9(X1,X2,X3)),X4),u1_struct_0(X2))|r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),X4)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.39  cnf(c_0_32, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (~r1_tarski(u1_struct_0(k4_waybel_9(esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_34, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(u1_struct_0(k4_waybel_9(X2,X1,X3)),u1_struct_0(X1))|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (l1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37])]), c_0_38]), c_0_39]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 41
% 0.19/0.39  # Proof object clause steps            : 24
% 0.19/0.39  # Proof object formula steps           : 17
% 0.19/0.39  # Proof object conjectures             : 10
% 0.19/0.39  # Proof object clause conjectures      : 7
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 16
% 0.19/0.39  # Proof object initial formulas used   : 8
% 0.19/0.39  # Proof object generating inferences   : 8
% 0.19/0.39  # Proof object simplifying inferences  : 9
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 8
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 29
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 29
% 0.19/0.39  # Processed clauses                    : 74
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 2
% 0.19/0.39  # ...remaining for further processing  : 72
% 0.19/0.39  # Other redundant clauses eliminated   : 1
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 0
% 0.19/0.39  # Generated clauses                    : 39
% 0.19/0.39  # ...of the previous two non-trivial   : 37
% 0.19/0.39  # Contextual simplify-reflections      : 5
% 0.19/0.39  # Paramodulations                      : 33
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 6
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 44
% 0.19/0.39  #    Positive orientable unit clauses  : 4
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 4
% 0.19/0.39  #    Non-unit-clauses                  : 36
% 0.19/0.39  # Current number of unprocessed clauses: 18
% 0.19/0.39  # ...number of literals in the above   : 286
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 27
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 2628
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 50
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 7
% 0.19/0.39  # Unit Clause-clause subsumption calls : 4
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 2
% 0.19/0.39  # BW rewrite match successes           : 0
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 5600
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.039 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.042 s
% 0.19/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
