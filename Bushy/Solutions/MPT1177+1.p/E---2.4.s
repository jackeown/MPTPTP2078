%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t84_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:23 EDT 2019

% Result     : Theorem 1.31s
% Output     : CNFRefutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 749 expanded)
%              Number of clauses        :   54 ( 259 expanded)
%              Number of leaves         :   15 ( 186 expanded)
%              Depth                    :   11
%              Number of atoms          :  535 (6435 expanded)
%              Number of equality atoms :   64 ( 289 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X2)
                 => ( r2_xboole_0(X3,X4)
                  <=> m1_orders_2(X3,X1,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t84_orders_2)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',commutativity_k3_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',redefinition_k9_subset_1)).

fof(d14_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k3_orders_2(X1,X2,X3) = k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',d14_orders_2)).

fof(d16_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v6_orders_2(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
             => ( m2_orders_2(X3,X1,X2)
              <=> ( X3 != k1_xboole_0
                  & r2_wellord1(u1_orders_2(X1),X3)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,X3)
                       => k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4))) = X4 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',d16_orders_2)).

fof(dt_m2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m2_orders_2(X3,X1,X2)
         => ( v6_orders_2(X3,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',dt_m2_orders_2)).

fof(t83_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X2)
                 => ( X3 != X4
                   => ( m1_orders_2(X3,X1,X4)
                    <=> ~ m1_orders_2(X4,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t83_orders_2)).

fof(d15_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( X2 != k1_xboole_0
                 => ( m1_orders_2(X3,X1,X2)
                  <=> ? [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                        & r2_hidden(X4,X2)
                        & X3 = k3_orders_2(X1,X2,X4) ) ) )
                & ( X2 = k1_xboole_0
                 => ( m1_orders_2(X3,X1,X2)
                  <=> X3 = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',d15_orders_2)).

fof(dt_m1_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m1_orders_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',dt_m1_orders_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t3_subset)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',d8_xboole_0)).

fof(antisymmetry_r2_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
     => ~ r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',antisymmetry_r2_xboole_0)).

fof(irreflexivity_r2_xboole_0,axiom,(
    ! [X1,X2] : ~ r2_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',irreflexivity_r2_xboole_0)).

fof(t68_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ ( X2 != k1_xboole_0
                & m1_orders_2(X2,X1,X2) )
            & ~ ( ~ m1_orders_2(X2,X1,X2)
                & X2 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t68_orders_2)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m2_orders_2(X3,X1,X2)
               => ! [X4] :
                    ( m2_orders_2(X4,X1,X2)
                   => ( r2_xboole_0(X3,X4)
                    <=> m1_orders_2(X3,X1,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t84_orders_2])).

fof(c_0_16,plain,(
    ! [X103,X104] : r1_tarski(k3_xboole_0(X103,X104),X103) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_17,plain,(
    ! [X14,X15] : k3_xboole_0(X14,X15) = k3_xboole_0(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_18,plain,(
    ! [X100,X101,X102] :
      ( ~ m1_subset_1(X102,k1_zfmisc_1(X100))
      | k9_subset_1(X100,X101,X102) = k3_xboole_0(X101,X102) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_19,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ v3_orders_2(X19)
      | ~ v4_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | k3_orders_2(X19,X20,X21) = k9_subset_1(u1_struct_0(X19),k2_orders_2(X19,k6_domain_1(u1_struct_0(X19),X21)),X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d14_orders_2])])])])).

fof(c_0_20,plain,(
    ! [X27,X28,X29,X30] :
      ( ( X29 != k1_xboole_0
        | ~ m2_orders_2(X29,X27,X28)
        | ~ v6_orders_2(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( r2_wellord1(u1_orders_2(X27),X29)
        | ~ m2_orders_2(X29,X27,X28)
        | ~ v6_orders_2(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r2_hidden(X30,X29)
        | k1_funct_1(X28,k1_orders_2(X27,k3_orders_2(X27,X29,X30))) = X30
        | ~ m2_orders_2(X29,X27,X28)
        | ~ v6_orders_2(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(esk6_3(X27,X28,X29),u1_struct_0(X27))
        | X29 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X27),X29)
        | m2_orders_2(X29,X27,X28)
        | ~ v6_orders_2(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( r2_hidden(esk6_3(X27,X28,X29),X29)
        | X29 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X27),X29)
        | m2_orders_2(X29,X27,X28)
        | ~ v6_orders_2(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( k1_funct_1(X28,k1_orders_2(X27,k3_orders_2(X27,X29,esk6_3(X27,X28,X29)))) != esk6_3(X27,X28,X29)
        | X29 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X27),X29)
        | m2_orders_2(X29,X27,X28)
        | ~ v6_orders_2(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).

fof(c_0_21,plain,(
    ! [X56,X57,X58] :
      ( ( v6_orders_2(X58,X56)
        | ~ m2_orders_2(X58,X56,X57)
        | v2_struct_0(X56)
        | ~ v3_orders_2(X56)
        | ~ v4_orders_2(X56)
        | ~ v5_orders_2(X56)
        | ~ l1_orders_2(X56)
        | ~ m1_orders_1(X57,k1_orders_1(u1_struct_0(X56))) )
      & ( m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ m2_orders_2(X58,X56,X57)
        | v2_struct_0(X56)
        | ~ v3_orders_2(X56)
        | ~ v4_orders_2(X56)
        | ~ v5_orders_2(X56)
        | ~ l1_orders_2(X56)
        | ~ m1_orders_1(X57,k1_orders_1(u1_struct_0(X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

fof(c_0_22,plain,(
    ! [X128,X129,X130,X131] :
      ( ( ~ m1_orders_2(X130,X128,X131)
        | ~ m1_orders_2(X131,X128,X130)
        | X130 = X131
        | ~ m2_orders_2(X131,X128,X129)
        | ~ m2_orders_2(X130,X128,X129)
        | ~ m1_orders_1(X129,k1_orders_1(u1_struct_0(X128)))
        | v2_struct_0(X128)
        | ~ v3_orders_2(X128)
        | ~ v4_orders_2(X128)
        | ~ v5_orders_2(X128)
        | ~ l1_orders_2(X128) )
      & ( m1_orders_2(X131,X128,X130)
        | m1_orders_2(X130,X128,X131)
        | X130 = X131
        | ~ m2_orders_2(X131,X128,X129)
        | ~ m2_orders_2(X130,X128,X129)
        | ~ m1_orders_1(X129,k1_orders_1(u1_struct_0(X128)))
        | v2_struct_0(X128)
        | ~ v3_orders_2(X128)
        | ~ v4_orders_2(X128)
        | ~ v5_orders_2(X128)
        | ~ l1_orders_2(X128) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0)))
    & m2_orders_2(esk3_0,esk1_0,esk2_0)
    & m2_orders_2(esk4_0,esk1_0,esk2_0)
    & ( ~ r2_xboole_0(esk3_0,esk4_0)
      | ~ m1_orders_2(esk3_0,esk1_0,esk4_0) )
    & ( r2_xboole_0(esk3_0,esk4_0)
      | m1_orders_2(esk3_0,esk1_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | k3_orders_2(X1,X2,X3) = k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)),X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X22,X23,X24,X26] :
      ( ( m1_subset_1(esk5_3(X22,X23,X24),u1_struct_0(X22))
        | ~ m1_orders_2(X24,X22,X23)
        | X23 = k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk5_3(X22,X23,X24),X23)
        | ~ m1_orders_2(X24,X22,X23)
        | X23 = k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( X24 = k3_orders_2(X22,X23,esk5_3(X22,X23,X24))
        | ~ m1_orders_2(X24,X22,X23)
        | X23 = k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X22))
        | ~ r2_hidden(X26,X23)
        | X24 != k3_orders_2(X22,X23,X26)
        | m1_orders_2(X24,X22,X23)
        | X23 = k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_orders_2(X24,X22,X23)
        | X24 = k1_xboole_0
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( X24 != k1_xboole_0
        | m1_orders_2(X24,X22,X23)
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).

fof(c_0_29,plain,(
    ! [X53,X54,X55] :
      ( v2_struct_0(X53)
      | ~ v3_orders_2(X53)
      | ~ v4_orders_2(X53)
      | ~ v5_orders_2(X53)
      | ~ l1_orders_2(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | ~ m1_orders_2(X55,X53,X54)
      | m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).

fof(c_0_30,plain,(
    ! [X114,X115] :
      ( ( ~ m1_subset_1(X114,k1_zfmisc_1(X115))
        | r1_tarski(X114,X115) )
      & ( ~ r1_tarski(X114,X115)
        | m1_subset_1(X114,k1_zfmisc_1(X115)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_31,plain,(
    ! [X32,X33] :
      ( ( r1_tarski(X32,X33)
        | ~ r2_xboole_0(X32,X33) )
      & ( X32 != X33
        | ~ r2_xboole_0(X32,X33) )
      & ( ~ r1_tarski(X32,X33)
        | X32 = X33
        | r2_xboole_0(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_32,plain,
    ( v2_struct_0(X2)
    | X1 != k1_xboole_0
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( v6_orders_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( m1_orders_2(X1,X2,X3)
    | m1_orders_2(X3,X2,X1)
    | X3 = X1
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X4)
    | ~ m2_orders_2(X3,X2,X4)
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)),X3) = k3_orders_2(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_44,plain,
    ( X1 = k3_orders_2(X2,X3,esk5_3(X2,X3,X1))
    | X3 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | X2 != k1_xboole_0
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( X1 = X2
    | m1_orders_2(X2,esk1_0,X1)
    | m1_orders_2(X1,esk1_0,X2)
    | ~ m2_orders_2(X2,esk1_0,esk2_0)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( m2_orders_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_orders_2(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( k3_orders_2(X1,X2,esk5_3(X1,X2,X3)) = X3
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk5_3(X2,X1,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_orders_2(X3,X2,X1)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r2_xboole_0(esk3_0,esk4_0)
    | m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_59,negated_conjecture,
    ( X1 = esk4_0
    | m1_orders_2(X1,esk1_0,esk4_0)
    | m1_orders_2(esk4_0,esk1_0,X1)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( m2_orders_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_61,plain,(
    ! [X12,X13] :
      ( ~ r2_xboole_0(X12,X13)
      | ~ r2_xboole_0(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_xboole_0])])])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_orders_2(X2,X3,X1)
    | ~ l1_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v3_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0))
    | m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_51])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( esk4_0 = esk3_0
    | m1_orders_2(esk4_0,esk1_0,esk3_0)
    | m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_60])).

cnf(c_0_70,plain,
    ( ~ r2_xboole_0(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_65]),c_0_41]),c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( esk4_0 = esk3_0
    | r1_tarski(esk4_0,esk3_0)
    | m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_67]),c_0_68]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_69]),c_0_41])).

cnf(c_0_74,negated_conjecture,
    ( m1_orders_2(esk3_0,esk1_0,esk4_0)
    | ~ r2_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_56])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_xboole_0(esk3_0,esk4_0)
    | ~ m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_76,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( esk4_0 = esk3_0
    | m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_73]),c_0_74])).

fof(c_0_78,plain,(
    ! [X93] : ~ r2_xboole_0(X93,X93) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).

fof(c_0_79,plain,(
    ! [X123,X124] :
      ( ( X124 = k1_xboole_0
        | ~ m1_orders_2(X124,X123,X124)
        | ~ m1_subset_1(X124,k1_zfmisc_1(u1_struct_0(X123)))
        | v2_struct_0(X123)
        | ~ v3_orders_2(X123)
        | ~ v4_orders_2(X123)
        | ~ v5_orders_2(X123)
        | ~ l1_orders_2(X123) )
      & ( m1_orders_2(X124,X123,X124)
        | X124 != k1_xboole_0
        | ~ m1_subset_1(X124,k1_zfmisc_1(u1_struct_0(X123)))
        | v2_struct_0(X123)
        | ~ v3_orders_2(X123)
        | ~ v4_orders_2(X123)
        | ~ v5_orders_2(X123)
        | ~ l1_orders_2(X123) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_orders_2])])])])])).

cnf(c_0_80,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_81,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X1,X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( m1_orders_2(esk3_0,esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_80]),c_0_80]),c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_68]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_69]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
