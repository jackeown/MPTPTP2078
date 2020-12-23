%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:35 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 402 expanded)
%              Number of clauses        :   49 ( 146 expanded)
%              Number of leaves         :   16 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  434 (2326 expanded)
%              Number of equality atoms :   50 ( 103 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal clause size      :  110 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_waybel_9)).

fof(dt_k4_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
        & l1_waybel_0(k4_waybel_9(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(t14_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ( v2_yellow_6(k4_waybel_9(X1,X2,X3),X1,X2)
                & m1_yellow_6(k4_waybel_9(X1,X2,X3),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_waybel_9)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(dt_k1_toler_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => m1_subset_1(k1_toler_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_toler_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(redefinition_k1_toler_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => k1_toler_1(X1,X2) = k2_wellord1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_toler_1)).

fof(t13_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).

fof(d9_yellow_6,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_6(X3,X1,X2)
             => ( v2_yellow_6(X3,X1,X2)
              <=> ( v4_yellow_0(X3,X2)
                  & m1_yellow_0(X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_6)).

fof(d14_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
          <=> u1_orders_2(X2) = k1_toler_1(u1_orders_2(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_yellow_0)).

fof(d8_yellow_6,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( l1_waybel_0(X3,X1)
             => ( m1_yellow_6(X3,X1,X2)
              <=> ( m1_yellow_0(X3,X2)
                  & u1_waybel_0(X1,X3) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(c_0_16,plain,(
    ! [X35,X36,X37,X38,X39,X41,X42,X44] :
      ( ( m1_subset_1(esk1_5(X35,X36,X37,X38,X39),u1_struct_0(X36))
        | ~ r2_hidden(X39,u1_struct_0(X38))
        | X38 != k4_waybel_9(X35,X36,X37)
        | ~ v6_waybel_0(X38,X35)
        | ~ l1_waybel_0(X38,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( esk1_5(X35,X36,X37,X38,X39) = X39
        | ~ r2_hidden(X39,u1_struct_0(X38))
        | X38 != k4_waybel_9(X35,X36,X37)
        | ~ v6_waybel_0(X38,X35)
        | ~ l1_waybel_0(X38,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( r1_orders_2(X36,X37,esk1_5(X35,X36,X37,X38,X39))
        | ~ r2_hidden(X39,u1_struct_0(X38))
        | X38 != k4_waybel_9(X35,X36,X37)
        | ~ v6_waybel_0(X38,X35)
        | ~ l1_waybel_0(X38,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( ~ m1_subset_1(X42,u1_struct_0(X36))
        | X42 != X41
        | ~ r1_orders_2(X36,X37,X42)
        | r2_hidden(X41,u1_struct_0(X38))
        | X38 != k4_waybel_9(X35,X36,X37)
        | ~ v6_waybel_0(X38,X35)
        | ~ l1_waybel_0(X38,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( r2_relset_1(u1_struct_0(X38),u1_struct_0(X38),u1_orders_2(X38),k1_toler_1(u1_orders_2(X36),u1_struct_0(X38)))
        | X38 != k4_waybel_9(X35,X36,X37)
        | ~ v6_waybel_0(X38,X35)
        | ~ l1_waybel_0(X38,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( u1_waybel_0(X35,X38) = k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36),u1_struct_0(X38))
        | X38 != k4_waybel_9(X35,X36,X37)
        | ~ v6_waybel_0(X38,X35)
        | ~ l1_waybel_0(X38,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( ~ r2_hidden(esk2_4(X35,X36,X37,X38),u1_struct_0(X38))
        | ~ m1_subset_1(X44,u1_struct_0(X36))
        | X44 != esk2_4(X35,X36,X37,X38)
        | ~ r1_orders_2(X36,X37,X44)
        | ~ r2_relset_1(u1_struct_0(X38),u1_struct_0(X38),u1_orders_2(X38),k1_toler_1(u1_orders_2(X36),u1_struct_0(X38)))
        | u1_waybel_0(X35,X38) != k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36),u1_struct_0(X38))
        | X38 = k4_waybel_9(X35,X36,X37)
        | ~ v6_waybel_0(X38,X35)
        | ~ l1_waybel_0(X38,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( m1_subset_1(esk3_4(X35,X36,X37,X38),u1_struct_0(X36))
        | r2_hidden(esk2_4(X35,X36,X37,X38),u1_struct_0(X38))
        | ~ r2_relset_1(u1_struct_0(X38),u1_struct_0(X38),u1_orders_2(X38),k1_toler_1(u1_orders_2(X36),u1_struct_0(X38)))
        | u1_waybel_0(X35,X38) != k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36),u1_struct_0(X38))
        | X38 = k4_waybel_9(X35,X36,X37)
        | ~ v6_waybel_0(X38,X35)
        | ~ l1_waybel_0(X38,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( esk3_4(X35,X36,X37,X38) = esk2_4(X35,X36,X37,X38)
        | r2_hidden(esk2_4(X35,X36,X37,X38),u1_struct_0(X38))
        | ~ r2_relset_1(u1_struct_0(X38),u1_struct_0(X38),u1_orders_2(X38),k1_toler_1(u1_orders_2(X36),u1_struct_0(X38)))
        | u1_waybel_0(X35,X38) != k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36),u1_struct_0(X38))
        | X38 = k4_waybel_9(X35,X36,X37)
        | ~ v6_waybel_0(X38,X35)
        | ~ l1_waybel_0(X38,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( r1_orders_2(X36,X37,esk3_4(X35,X36,X37,X38))
        | r2_hidden(esk2_4(X35,X36,X37,X38),u1_struct_0(X38))
        | ~ r2_relset_1(u1_struct_0(X38),u1_struct_0(X38),u1_orders_2(X38),k1_toler_1(u1_orders_2(X36),u1_struct_0(X38)))
        | u1_waybel_0(X35,X38) != k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36),u1_struct_0(X38))
        | X38 = k4_waybel_9(X35,X36,X37)
        | ~ v6_waybel_0(X38,X35)
        | ~ l1_waybel_0(X38,X35)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).

fof(c_0_17,plain,(
    ! [X46,X47,X48] :
      ( ( v6_waybel_0(k4_waybel_9(X46,X47,X48),X46)
        | v2_struct_0(X46)
        | ~ l1_struct_0(X46)
        | v2_struct_0(X47)
        | ~ l1_waybel_0(X47,X46)
        | ~ m1_subset_1(X48,u1_struct_0(X47)) )
      & ( l1_waybel_0(k4_waybel_9(X46,X47,X48),X46)
        | v2_struct_0(X46)
        | ~ l1_struct_0(X46)
        | v2_struct_0(X47)
        | ~ l1_waybel_0(X47,X46)
        | ~ m1_subset_1(X48,u1_struct_0(X47)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => ( v2_yellow_6(k4_waybel_9(X1,X2,X3),X1,X2)
                  & m1_yellow_6(k4_waybel_9(X1,X2,X3),X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_waybel_9])).

cnf(c_0_19,plain,
    ( r2_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1),k1_toler_1(u1_orders_2(X2),u1_struct_0(X1)))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | X1 != k4_waybel_9(X3,X2,X4)
    | ~ v6_waybel_0(X1,X3)
    | ~ l1_waybel_0(X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_struct_0(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & l1_waybel_0(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ( ~ v2_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0)
      | ~ m1_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_23,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r2_relset_1(X14,X15,X16,X17)
        | X16 = X17
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( X16 != X17
        | r2_relset_1(X14,X15,X16,X17)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_24,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | m1_subset_1(k1_toler_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X24,X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_toler_1])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_orders_2(k4_waybel_9(X1,X2,X3)),k1_toler_1(u1_orders_2(X2),u1_struct_0(k4_waybel_9(X1,X2,X3))))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(k1_toler_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_relset_1(u1_struct_0(k4_waybel_9(X1,esk5_0,esk6_0)),u1_struct_0(k4_waybel_9(X1,esk5_0,esk6_0)),u1_orders_2(k4_waybel_9(X1,esk5_0,esk6_0)),k1_toler_1(u1_orders_2(esk5_0),u1_struct_0(k4_waybel_9(X1,esk5_0,esk6_0))))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_35,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | m1_subset_1(u1_orders_2(X18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X18)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_36,plain,(
    ! [X27,X28] :
      ( ~ l1_struct_0(X27)
      | ~ l1_waybel_0(X28,X27)
      | l1_orders_2(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_37,plain,
    ( X1 = k1_toler_1(X2,X3)
    | ~ r2_relset_1(X3,X3,X1,k1_toler_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r2_relset_1(u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0)),k1_toler_1(u1_orders_2(esk5_0),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v2_struct_0(X1)
    | l1_waybel_0(k4_waybel_9(X1,esk5_0,esk6_0),X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_27])).

cnf(c_0_43,plain,
    ( u1_waybel_0(X1,X2) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),u1_struct_0(X2))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | X2 != k4_waybel_9(X1,X3,X4)
    | ~ v6_waybel_0(X2,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_44,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_45,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | k2_wellord1(X9,X10) = k3_xboole_0(X9,k2_zfmisc_1(X10,X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_46,negated_conjecture,
    ( k1_toler_1(u1_orders_2(esk5_0),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0))) = u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)))))
    | ~ v1_relat_1(u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_32])])).

cnf(c_0_49,negated_conjecture,
    ( l1_waybel_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_50,plain,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(k4_waybel_9(X2,X1,X3))) = u1_waybel_0(X2,k4_waybel_9(X2,X1,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_20]),c_0_21])).

cnf(c_0_51,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_53,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | k1_toler_1(X25,X26) = k2_wellord1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_toler_1])])).

fof(c_0_54,plain,(
    ! [X49,X50,X51] :
      ( v2_struct_0(X49)
      | ~ l1_struct_0(X49)
      | v2_struct_0(X50)
      | ~ l1_waybel_0(X50,X49)
      | ~ m1_subset_1(X51,u1_struct_0(X50))
      | r1_tarski(u1_struct_0(k4_waybel_9(X49,X50,X51)),u1_struct_0(X50)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_waybel_9])])])])).

fof(c_0_55,plain,(
    ! [X32,X33,X34] :
      ( ( v4_yellow_0(X34,X33)
        | ~ v2_yellow_6(X34,X32,X33)
        | ~ m1_yellow_6(X34,X32,X33)
        | ~ l1_waybel_0(X33,X32)
        | ~ l1_struct_0(X32) )
      & ( m1_yellow_0(X34,X33)
        | ~ v2_yellow_6(X34,X32,X33)
        | ~ m1_yellow_6(X34,X32,X33)
        | ~ l1_waybel_0(X33,X32)
        | ~ l1_struct_0(X32) )
      & ( ~ v4_yellow_0(X34,X33)
        | ~ m1_yellow_0(X34,X33)
        | v2_yellow_6(X34,X32,X33)
        | ~ m1_yellow_6(X34,X32,X33)
        | ~ l1_waybel_0(X33,X32)
        | ~ l1_struct_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_6])])])])).

fof(c_0_56,plain,(
    ! [X21,X22] :
      ( ( ~ v4_yellow_0(X22,X21)
        | u1_orders_2(X22) = k1_toler_1(u1_orders_2(X21),u1_struct_0(X22))
        | ~ m1_yellow_0(X22,X21)
        | ~ l1_orders_2(X21) )
      & ( u1_orders_2(X22) != k1_toler_1(u1_orders_2(X21),u1_struct_0(X22))
        | v4_yellow_0(X22,X21)
        | ~ m1_yellow_0(X22,X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_yellow_0])])])])).

cnf(c_0_57,negated_conjecture,
    ( k1_toler_1(u1_orders_2(esk5_0),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0))) = u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_58,negated_conjecture,
    ( l1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_49]),c_0_32])])).

fof(c_0_59,plain,(
    ! [X29,X30,X31] :
      ( ( m1_yellow_0(X31,X30)
        | ~ m1_yellow_6(X31,X29,X30)
        | ~ l1_waybel_0(X31,X29)
        | ~ l1_waybel_0(X30,X29)
        | ~ l1_struct_0(X29) )
      & ( u1_waybel_0(X29,X31) = k2_partfun1(u1_struct_0(X30),u1_struct_0(X29),u1_waybel_0(X29,X30),u1_struct_0(X31))
        | ~ m1_yellow_6(X31,X29,X30)
        | ~ l1_waybel_0(X31,X29)
        | ~ l1_waybel_0(X30,X29)
        | ~ l1_struct_0(X29) )
      & ( ~ m1_yellow_0(X31,X30)
        | u1_waybel_0(X29,X31) != k2_partfun1(u1_struct_0(X30),u1_struct_0(X29),u1_waybel_0(X29,X30),u1_struct_0(X31))
        | m1_yellow_6(X31,X29,X30)
        | ~ l1_waybel_0(X31,X29)
        | ~ l1_waybel_0(X30,X29)
        | ~ l1_struct_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).

cnf(c_0_60,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(X1),u1_waybel_0(X1,esk5_0),u1_struct_0(k4_waybel_9(X1,esk5_0,esk6_0))) = u1_waybel_0(X1,k4_waybel_9(X1,esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_26]),c_0_27])).

cnf(c_0_61,plain,
    ( r1_tarski(k2_wellord1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,plain,
    ( k1_toler_1(X1,X2) = k2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0)
    | ~ m1_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_65,plain,
    ( v2_yellow_6(X1,X3,X2)
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( v4_yellow_0(X1,X2)
    | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X2),u1_struct_0(X1))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( k1_toler_1(u1_orders_2(esk5_0),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0))) = u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_40]),c_0_58])])).

cnf(c_0_68,plain,
    ( m1_yellow_6(X1,X3,X2)
    | ~ m1_yellow_0(X1,X2)
    | u1_waybel_0(X3,X1) != k2_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_waybel_0(X3,X2),u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0))) = u1_waybel_0(esk4_0,k4_waybel_9(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_31]),c_0_32])]),c_0_33])).

fof(c_0_70,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(u1_struct_0(X20),u1_struct_0(X19))
        | ~ m1_yellow_0(X20,X19)
        | ~ l1_orders_2(X20)
        | ~ l1_orders_2(X19) )
      & ( r1_tarski(u1_orders_2(X20),u1_orders_2(X19))
        | ~ m1_yellow_0(X20,X19)
        | ~ l1_orders_2(X20)
        | ~ l1_orders_2(X19) )
      & ( ~ r1_tarski(u1_struct_0(X20),u1_struct_0(X19))
        | ~ r1_tarski(u1_orders_2(X20),u1_orders_2(X19))
        | m1_yellow_0(X20,X19)
        | ~ l1_orders_2(X20)
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_toler_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_tarski(u1_struct_0(k4_waybel_9(X1,esk5_0,esk6_0)),u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_26]),c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( ~ m1_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0)
    | ~ v4_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0)
    | ~ m1_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_31]),c_0_32])])).

cnf(c_0_74,negated_conjecture,
    ( v4_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0)
    | ~ m1_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_48])])).

cnf(c_0_75,negated_conjecture,
    ( m1_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0)
    | ~ m1_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_31]),c_0_49]),c_0_32])])).

cnf(c_0_76,plain,
    ( m1_yellow_0(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_orders_2(esk5_0))
    | ~ v1_relat_1(u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_relat_1(u1_orders_2(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_48]),c_0_58]),c_0_78])]),c_0_79])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_47]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.14/0.39  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.030 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(d7_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>![X4]:((v6_waybel_0(X4,X1)&l1_waybel_0(X4,X1))=>(X4=k4_waybel_9(X1,X2,X3)<=>((![X5]:(r2_hidden(X5,u1_struct_0(X4))<=>?[X6]:((m1_subset_1(X6,u1_struct_0(X2))&X6=X5)&r1_orders_2(X2,X3,X6)))&r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4))))&u1_waybel_0(X1,X4)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_waybel_9)).
% 0.14/0.39  fof(dt_k4_waybel_9, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v2_struct_0(X2)))&l1_waybel_0(X2,X1))&m1_subset_1(X3,u1_struct_0(X2)))=>(v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)&l1_waybel_0(k4_waybel_9(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 0.14/0.39  fof(t14_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>(v2_yellow_6(k4_waybel_9(X1,X2,X3),X1,X2)&m1_yellow_6(k4_waybel_9(X1,X2,X3),X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_waybel_9)).
% 0.14/0.39  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.14/0.39  fof(dt_k1_toler_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>m1_subset_1(k1_toler_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_toler_1)).
% 0.14/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.14/0.39  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.14/0.39  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.14/0.39  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.14/0.39  fof(d6_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 0.14/0.39  fof(redefinition_k1_toler_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>k1_toler_1(X1,X2)=k2_wellord1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_toler_1)).
% 0.14/0.39  fof(t13_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_waybel_9)).
% 0.14/0.39  fof(d9_yellow_6, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(m1_yellow_6(X3,X1,X2)=>(v2_yellow_6(X3,X1,X2)<=>(v4_yellow_0(X3,X2)&m1_yellow_0(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_6)).
% 0.14/0.39  fof(d14_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_yellow_0(X2,X1)=>(v4_yellow_0(X2,X1)<=>u1_orders_2(X2)=k1_toler_1(u1_orders_2(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_yellow_0)).
% 0.14/0.39  fof(d8_yellow_6, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(l1_waybel_0(X3,X1)=>(m1_yellow_6(X3,X1,X2)<=>(m1_yellow_0(X3,X2)&u1_waybel_0(X1,X3)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_yellow_6)).
% 0.14/0.39  fof(d13_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(m1_yellow_0(X2,X1)<=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X1))&r1_tarski(u1_orders_2(X2),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_yellow_0)).
% 0.14/0.39  fof(c_0_16, plain, ![X35, X36, X37, X38, X39, X41, X42, X44]:(((((((m1_subset_1(esk1_5(X35,X36,X37,X38,X39),u1_struct_0(X36))|~r2_hidden(X39,u1_struct_0(X38))|X38!=k4_waybel_9(X35,X36,X37)|(~v6_waybel_0(X38,X35)|~l1_waybel_0(X38,X35))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35)))&(esk1_5(X35,X36,X37,X38,X39)=X39|~r2_hidden(X39,u1_struct_0(X38))|X38!=k4_waybel_9(X35,X36,X37)|(~v6_waybel_0(X38,X35)|~l1_waybel_0(X38,X35))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35))))&(r1_orders_2(X36,X37,esk1_5(X35,X36,X37,X38,X39))|~r2_hidden(X39,u1_struct_0(X38))|X38!=k4_waybel_9(X35,X36,X37)|(~v6_waybel_0(X38,X35)|~l1_waybel_0(X38,X35))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35))))&(~m1_subset_1(X42,u1_struct_0(X36))|X42!=X41|~r1_orders_2(X36,X37,X42)|r2_hidden(X41,u1_struct_0(X38))|X38!=k4_waybel_9(X35,X36,X37)|(~v6_waybel_0(X38,X35)|~l1_waybel_0(X38,X35))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35))))&(r2_relset_1(u1_struct_0(X38),u1_struct_0(X38),u1_orders_2(X38),k1_toler_1(u1_orders_2(X36),u1_struct_0(X38)))|X38!=k4_waybel_9(X35,X36,X37)|(~v6_waybel_0(X38,X35)|~l1_waybel_0(X38,X35))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35))))&(u1_waybel_0(X35,X38)=k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36),u1_struct_0(X38))|X38!=k4_waybel_9(X35,X36,X37)|(~v6_waybel_0(X38,X35)|~l1_waybel_0(X38,X35))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35))))&((~r2_hidden(esk2_4(X35,X36,X37,X38),u1_struct_0(X38))|(~m1_subset_1(X44,u1_struct_0(X36))|X44!=esk2_4(X35,X36,X37,X38)|~r1_orders_2(X36,X37,X44))|~r2_relset_1(u1_struct_0(X38),u1_struct_0(X38),u1_orders_2(X38),k1_toler_1(u1_orders_2(X36),u1_struct_0(X38)))|u1_waybel_0(X35,X38)!=k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36),u1_struct_0(X38))|X38=k4_waybel_9(X35,X36,X37)|(~v6_waybel_0(X38,X35)|~l1_waybel_0(X38,X35))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35)))&(((m1_subset_1(esk3_4(X35,X36,X37,X38),u1_struct_0(X36))|r2_hidden(esk2_4(X35,X36,X37,X38),u1_struct_0(X38))|~r2_relset_1(u1_struct_0(X38),u1_struct_0(X38),u1_orders_2(X38),k1_toler_1(u1_orders_2(X36),u1_struct_0(X38)))|u1_waybel_0(X35,X38)!=k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36),u1_struct_0(X38))|X38=k4_waybel_9(X35,X36,X37)|(~v6_waybel_0(X38,X35)|~l1_waybel_0(X38,X35))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35)))&(esk3_4(X35,X36,X37,X38)=esk2_4(X35,X36,X37,X38)|r2_hidden(esk2_4(X35,X36,X37,X38),u1_struct_0(X38))|~r2_relset_1(u1_struct_0(X38),u1_struct_0(X38),u1_orders_2(X38),k1_toler_1(u1_orders_2(X36),u1_struct_0(X38)))|u1_waybel_0(X35,X38)!=k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36),u1_struct_0(X38))|X38=k4_waybel_9(X35,X36,X37)|(~v6_waybel_0(X38,X35)|~l1_waybel_0(X38,X35))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35))))&(r1_orders_2(X36,X37,esk3_4(X35,X36,X37,X38))|r2_hidden(esk2_4(X35,X36,X37,X38),u1_struct_0(X38))|~r2_relset_1(u1_struct_0(X38),u1_struct_0(X38),u1_orders_2(X38),k1_toler_1(u1_orders_2(X36),u1_struct_0(X38)))|u1_waybel_0(X35,X38)!=k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36),u1_struct_0(X38))|X38=k4_waybel_9(X35,X36,X37)|(~v6_waybel_0(X38,X35)|~l1_waybel_0(X38,X35))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).
% 0.14/0.39  fof(c_0_17, plain, ![X46, X47, X48]:((v6_waybel_0(k4_waybel_9(X46,X47,X48),X46)|(v2_struct_0(X46)|~l1_struct_0(X46)|v2_struct_0(X47)|~l1_waybel_0(X47,X46)|~m1_subset_1(X48,u1_struct_0(X47))))&(l1_waybel_0(k4_waybel_9(X46,X47,X48),X46)|(v2_struct_0(X46)|~l1_struct_0(X46)|v2_struct_0(X47)|~l1_waybel_0(X47,X46)|~m1_subset_1(X48,u1_struct_0(X47))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).
% 0.14/0.39  fof(c_0_18, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>(v2_yellow_6(k4_waybel_9(X1,X2,X3),X1,X2)&m1_yellow_6(k4_waybel_9(X1,X2,X3),X1,X2)))))), inference(assume_negation,[status(cth)],[t14_waybel_9])).
% 0.14/0.39  cnf(c_0_19, plain, (r2_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1),k1_toler_1(u1_orders_2(X2),u1_struct_0(X1)))|v2_struct_0(X2)|v2_struct_0(X3)|X1!=k4_waybel_9(X3,X2,X4)|~v6_waybel_0(X1,X3)|~l1_waybel_0(X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_20, plain, (l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_21, plain, (v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  fof(c_0_22, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_struct_0(esk4_0))&((~v2_struct_0(esk5_0)&l1_waybel_0(esk5_0,esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(~v2_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0)|~m1_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.14/0.39  fof(c_0_23, plain, ![X14, X15, X16, X17]:((~r2_relset_1(X14,X15,X16,X17)|X16=X17|(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))&(X16!=X17|r2_relset_1(X14,X15,X16,X17)|(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.14/0.39  fof(c_0_24, plain, ![X23, X24]:(~v1_relat_1(X23)|m1_subset_1(k1_toler_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(X24,X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_toler_1])])).
% 0.14/0.39  cnf(c_0_25, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_orders_2(k4_waybel_9(X1,X2,X3)),k1_toler_1(u1_orders_2(X2),u1_struct_0(k4_waybel_9(X1,X2,X3))))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_20]), c_0_21])).
% 0.14/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_28, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_29, plain, (m1_subset_1(k1_toler_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (v2_struct_0(X1)|r2_relset_1(u1_struct_0(k4_waybel_9(X1,esk5_0,esk6_0)),u1_struct_0(k4_waybel_9(X1,esk5_0,esk6_0)),u1_orders_2(k4_waybel_9(X1,esk5_0,esk6_0)),k1_toler_1(u1_orders_2(esk5_0),u1_struct_0(k4_waybel_9(X1,esk5_0,esk6_0))))|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.14/0.39  cnf(c_0_31, negated_conjecture, (l1_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (l1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  fof(c_0_34, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.14/0.39  fof(c_0_35, plain, ![X18]:(~l1_orders_2(X18)|m1_subset_1(u1_orders_2(X18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X18))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.14/0.39  fof(c_0_36, plain, ![X27, X28]:(~l1_struct_0(X27)|(~l1_waybel_0(X28,X27)|l1_orders_2(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.14/0.39  cnf(c_0_37, plain, (X1=k1_toler_1(X2,X3)|~r2_relset_1(X3,X3,X1,k1_toler_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (r2_relset_1(u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0)),k1_toler_1(u1_orders_2(esk5_0),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_33])).
% 0.14/0.39  cnf(c_0_39, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.39  cnf(c_0_40, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.39  cnf(c_0_41, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (v2_struct_0(X1)|l1_waybel_0(k4_waybel_9(X1,esk5_0,esk6_0),X1)|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_26]), c_0_27])).
% 0.14/0.39  cnf(c_0_43, plain, (u1_waybel_0(X1,X2)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),u1_struct_0(X2))|v2_struct_0(X3)|v2_struct_0(X1)|X2!=k4_waybel_9(X1,X3,X4)|~v6_waybel_0(X2,X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X4,u1_struct_0(X3))|~l1_waybel_0(X3,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  fof(c_0_44, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.14/0.39  fof(c_0_45, plain, ![X9, X10]:(~v1_relat_1(X9)|k2_wellord1(X9,X10)=k3_xboole_0(X9,k2_zfmisc_1(X10,X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (k1_toler_1(u1_orders_2(esk5_0),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)))=u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0))|~m1_subset_1(u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)))))|~v1_relat_1(u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.39  cnf(c_0_47, plain, (v1_relat_1(u1_orders_2(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.39  cnf(c_0_48, negated_conjecture, (l1_orders_2(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_31]), c_0_32])])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (l1_waybel_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_31]), c_0_32])]), c_0_33])).
% 0.14/0.39  cnf(c_0_50, plain, (k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(k4_waybel_9(X2,X1,X3)))=u1_waybel_0(X2,k4_waybel_9(X2,X1,X3))|v2_struct_0(X1)|v2_struct_0(X2)|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]), c_0_20]), c_0_21])).
% 0.14/0.39  cnf(c_0_51, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.39  cnf(c_0_52, plain, (k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.39  fof(c_0_53, plain, ![X25, X26]:(~v1_relat_1(X25)|k1_toler_1(X25,X26)=k2_wellord1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_toler_1])])).
% 0.14/0.39  fof(c_0_54, plain, ![X49, X50, X51]:(v2_struct_0(X49)|~l1_struct_0(X49)|(v2_struct_0(X50)|~l1_waybel_0(X50,X49)|(~m1_subset_1(X51,u1_struct_0(X50))|r1_tarski(u1_struct_0(k4_waybel_9(X49,X50,X51)),u1_struct_0(X50))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_waybel_9])])])])).
% 0.14/0.39  fof(c_0_55, plain, ![X32, X33, X34]:(((v4_yellow_0(X34,X33)|~v2_yellow_6(X34,X32,X33)|~m1_yellow_6(X34,X32,X33)|~l1_waybel_0(X33,X32)|~l1_struct_0(X32))&(m1_yellow_0(X34,X33)|~v2_yellow_6(X34,X32,X33)|~m1_yellow_6(X34,X32,X33)|~l1_waybel_0(X33,X32)|~l1_struct_0(X32)))&(~v4_yellow_0(X34,X33)|~m1_yellow_0(X34,X33)|v2_yellow_6(X34,X32,X33)|~m1_yellow_6(X34,X32,X33)|~l1_waybel_0(X33,X32)|~l1_struct_0(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_6])])])])).
% 0.14/0.39  fof(c_0_56, plain, ![X21, X22]:((~v4_yellow_0(X22,X21)|u1_orders_2(X22)=k1_toler_1(u1_orders_2(X21),u1_struct_0(X22))|~m1_yellow_0(X22,X21)|~l1_orders_2(X21))&(u1_orders_2(X22)!=k1_toler_1(u1_orders_2(X21),u1_struct_0(X22))|v4_yellow_0(X22,X21)|~m1_yellow_0(X22,X21)|~l1_orders_2(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_yellow_0])])])])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, (k1_toler_1(u1_orders_2(esk5_0),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)))=u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0))|~m1_subset_1(u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (l1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_49]), c_0_32])])).
% 0.14/0.39  fof(c_0_59, plain, ![X29, X30, X31]:(((m1_yellow_0(X31,X30)|~m1_yellow_6(X31,X29,X30)|~l1_waybel_0(X31,X29)|~l1_waybel_0(X30,X29)|~l1_struct_0(X29))&(u1_waybel_0(X29,X31)=k2_partfun1(u1_struct_0(X30),u1_struct_0(X29),u1_waybel_0(X29,X30),u1_struct_0(X31))|~m1_yellow_6(X31,X29,X30)|~l1_waybel_0(X31,X29)|~l1_waybel_0(X30,X29)|~l1_struct_0(X29)))&(~m1_yellow_0(X31,X30)|u1_waybel_0(X29,X31)!=k2_partfun1(u1_struct_0(X30),u1_struct_0(X29),u1_waybel_0(X29,X30),u1_struct_0(X31))|m1_yellow_6(X31,X29,X30)|~l1_waybel_0(X31,X29)|~l1_waybel_0(X30,X29)|~l1_struct_0(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(X1),u1_waybel_0(X1,esk5_0),u1_struct_0(k4_waybel_9(X1,esk5_0,esk6_0)))=u1_waybel_0(X1,k4_waybel_9(X1,esk5_0,esk6_0))|v2_struct_0(X1)|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_26]), c_0_27])).
% 0.14/0.39  cnf(c_0_61, plain, (r1_tarski(k2_wellord1(X1,X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.14/0.39  cnf(c_0_62, plain, (k1_toler_1(X1,X2)=k2_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.14/0.39  cnf(c_0_63, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.14/0.39  cnf(c_0_64, negated_conjecture, (~v2_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0)|~m1_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_65, plain, (v2_yellow_6(X1,X3,X2)|~v4_yellow_0(X1,X2)|~m1_yellow_0(X1,X2)|~m1_yellow_6(X1,X3,X2)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.14/0.39  cnf(c_0_66, plain, (v4_yellow_0(X1,X2)|u1_orders_2(X1)!=k1_toler_1(u1_orders_2(X2),u1_struct_0(X1))|~m1_yellow_0(X1,X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.14/0.39  cnf(c_0_67, negated_conjecture, (k1_toler_1(u1_orders_2(esk5_0),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)))=u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_40]), c_0_58])])).
% 0.14/0.39  cnf(c_0_68, plain, (m1_yellow_6(X1,X3,X2)|~m1_yellow_0(X1,X2)|u1_waybel_0(X3,X1)!=k2_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_waybel_0(X3,X2),u1_struct_0(X1))|~l1_waybel_0(X1,X3)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.14/0.39  cnf(c_0_69, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0),u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)))=u1_waybel_0(esk4_0,k4_waybel_9(esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_31]), c_0_32])]), c_0_33])).
% 0.14/0.39  fof(c_0_70, plain, ![X19, X20]:(((r1_tarski(u1_struct_0(X20),u1_struct_0(X19))|~m1_yellow_0(X20,X19)|~l1_orders_2(X20)|~l1_orders_2(X19))&(r1_tarski(u1_orders_2(X20),u1_orders_2(X19))|~m1_yellow_0(X20,X19)|~l1_orders_2(X20)|~l1_orders_2(X19)))&(~r1_tarski(u1_struct_0(X20),u1_struct_0(X19))|~r1_tarski(u1_orders_2(X20),u1_orders_2(X19))|m1_yellow_0(X20,X19)|~l1_orders_2(X20)|~l1_orders_2(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).
% 0.14/0.39  cnf(c_0_71, plain, (r1_tarski(k1_toler_1(X1,X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.14/0.39  cnf(c_0_72, negated_conjecture, (v2_struct_0(X1)|r1_tarski(u1_struct_0(k4_waybel_9(X1,esk5_0,esk6_0)),u1_struct_0(esk5_0))|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_26]), c_0_27])).
% 0.14/0.39  cnf(c_0_73, negated_conjecture, (~m1_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0)|~v4_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0)|~m1_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_31]), c_0_32])])).
% 0.14/0.39  cnf(c_0_74, negated_conjecture, (v4_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0)|~m1_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_48])])).
% 0.14/0.39  cnf(c_0_75, negated_conjecture, (m1_yellow_6(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk4_0,esk5_0)|~m1_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_31]), c_0_49]), c_0_32])])).
% 0.14/0.39  cnf(c_0_76, plain, (m1_yellow_0(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~r1_tarski(u1_orders_2(X1),u1_orders_2(X2))|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.14/0.39  cnf(c_0_77, negated_conjecture, (r1_tarski(u1_orders_2(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_orders_2(esk5_0))|~v1_relat_1(u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_71, c_0_67])).
% 0.14/0.39  cnf(c_0_78, negated_conjecture, (r1_tarski(u1_struct_0(k4_waybel_9(esk4_0,esk5_0,esk6_0)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_31]), c_0_32])]), c_0_33])).
% 0.14/0.39  cnf(c_0_79, negated_conjecture, (~m1_yellow_0(k4_waybel_9(esk4_0,esk5_0,esk6_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.14/0.39  cnf(c_0_80, negated_conjecture, (~v1_relat_1(u1_orders_2(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_48]), c_0_58]), c_0_78])]), c_0_79])).
% 0.14/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_47]), c_0_48])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 82
% 0.14/0.39  # Proof object clause steps            : 49
% 0.14/0.39  # Proof object formula steps           : 33
% 0.14/0.39  # Proof object conjectures             : 29
% 0.14/0.39  # Proof object clause conjectures      : 26
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 23
% 0.14/0.39  # Proof object initial formulas used   : 16
% 0.14/0.39  # Proof object generating inferences   : 24
% 0.14/0.39  # Proof object simplifying inferences  : 47
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 16
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 39
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 39
% 0.14/0.39  # Processed clauses                    : 129
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 2
% 0.14/0.39  # ...remaining for further processing  : 127
% 0.14/0.39  # Other redundant clauses eliminated   : 9
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 1
% 0.14/0.39  # Backward-rewritten                   : 2
% 0.14/0.39  # Generated clauses                    : 81
% 0.14/0.39  # ...of the previous two non-trivial   : 74
% 0.14/0.39  # Contextual simplify-reflections      : 20
% 0.14/0.39  # Paramodulations                      : 73
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 9
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
% 0.14/0.39  # Current number of processed clauses  : 77
% 0.14/0.39  #    Positive orientable unit clauses  : 12
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 4
% 0.14/0.39  #    Non-unit-clauses                  : 61
% 0.14/0.39  # Current number of unprocessed clauses: 23
% 0.14/0.39  # ...number of literals in the above   : 183
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 42
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 4390
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 258
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 22
% 0.14/0.39  # Unit Clause-clause subsumption calls : 93
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 7
% 0.14/0.39  # BW rewrite match successes           : 1
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 8630
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.043 s
% 0.14/0.39  # System time              : 0.005 s
% 0.14/0.39  # Total time               : 0.048 s
% 0.14/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
