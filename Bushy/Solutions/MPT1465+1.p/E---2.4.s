%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t60_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:10 EDT 2019

% Result     : Theorem 172.72s
% Output     : CNFRefutation 172.72s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 618 expanded)
%              Number of clauses        :   58 ( 191 expanded)
%              Number of leaves         :   14 ( 159 expanded)
%              Depth                    :   14
%              Number of atoms          :  546 (6539 expanded)
%              Number of equality atoms :   20 (  45 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal clause size      :   30 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v3_filter_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v19_lattices(X2,X1)
            & v20_lattices(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ( ( r2_hidden(X3,k6_eqrel_1(u1_struct_0(X1),u1_struct_0(X1),k9_filter_0(X1,X2),X4))
                          & r2_hidden(X5,k6_eqrel_1(u1_struct_0(X1),u1_struct_0(X1),k9_filter_0(X1,X2),X4)) )
                       => ( r2_hidden(k3_lattices(X1,X3,X5),k6_eqrel_1(u1_struct_0(X1),u1_struct_0(X1),k9_filter_0(X1,X2),X4))
                          & r2_hidden(k4_lattices(X1,X3,X5),k6_eqrel_1(u1_struct_0(X1),u1_struct_0(X1),k9_filter_0(X1,X2),X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',t60_filter_1)).

fof(l72_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v3_filter_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v19_lattices(X2,X1)
            & v20_lattices(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X3,k6_eqrel_1(u1_struct_0(X1),u1_struct_0(X1),k9_filter_0(X1,X2),X4))
                  <=> r2_hidden(k7_filter_0(X1,X3,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',l72_filter_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',t7_boole)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',commutativity_k4_lattices)).

fof(d11_filter_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_filter_0(X1,X2,X3) = k4_lattices(X1,k4_filter_0(X1,X2,X3),k4_filter_0(X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',d11_filter_0)).

fof(dt_k4_filter_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',dt_k4_filter_0)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',cc1_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',dt_l3_lattices)).

fof(t17_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k1_lattices(X1,X2,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',t17_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',redefinition_k3_lattices)).

fof(t59_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v3_filter_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v19_lattices(X2,X1)
            & v20_lattices(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X1))
                         => ( ( r2_hidden(k7_filter_0(X1,X3,X4),X2)
                              & r2_hidden(k7_filter_0(X1,X5,X6),X2) )
                           => ( r2_hidden(k7_filter_0(X1,k3_lattices(X1,X3,X5),k3_lattices(X1,X4,X6)),X2)
                              & r2_hidden(k7_filter_0(X1,k4_lattices(X1,X3,X5),k4_lattices(X1,X4,X6)),X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',t59_filter_1)).

fof(t18_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,X2,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',t18_lattices)).

fof(dt_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',dt_k3_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t60_filter_1.p',dt_k4_lattices)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v3_filter_0(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v19_lattices(X2,X1)
              & v20_lattices(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ( ( r2_hidden(X3,k6_eqrel_1(u1_struct_0(X1),u1_struct_0(X1),k9_filter_0(X1,X2),X4))
                            & r2_hidden(X5,k6_eqrel_1(u1_struct_0(X1),u1_struct_0(X1),k9_filter_0(X1,X2),X4)) )
                         => ( r2_hidden(k3_lattices(X1,X3,X5),k6_eqrel_1(u1_struct_0(X1),u1_struct_0(X1),k9_filter_0(X1,X2),X4))
                            & r2_hidden(k4_lattices(X1,X3,X5),k6_eqrel_1(u1_struct_0(X1),u1_struct_0(X1),k9_filter_0(X1,X2),X4)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t60_filter_1])).

fof(c_0_15,plain,(
    ! [X177,X178,X179,X180] :
      ( ( ~ r2_hidden(X179,k6_eqrel_1(u1_struct_0(X177),u1_struct_0(X177),k9_filter_0(X177,X178),X180))
        | r2_hidden(k7_filter_0(X177,X179,X180),X178)
        | ~ m1_subset_1(X180,u1_struct_0(X177))
        | ~ m1_subset_1(X179,u1_struct_0(X177))
        | v1_xboole_0(X178)
        | ~ v19_lattices(X178,X177)
        | ~ v20_lattices(X178,X177)
        | ~ m1_subset_1(X178,k1_zfmisc_1(u1_struct_0(X177)))
        | v2_struct_0(X177)
        | ~ v10_lattices(X177)
        | ~ v3_filter_0(X177)
        | ~ l3_lattices(X177) )
      & ( ~ r2_hidden(k7_filter_0(X177,X179,X180),X178)
        | r2_hidden(X179,k6_eqrel_1(u1_struct_0(X177),u1_struct_0(X177),k9_filter_0(X177,X178),X180))
        | ~ m1_subset_1(X180,u1_struct_0(X177))
        | ~ m1_subset_1(X179,u1_struct_0(X177))
        | v1_xboole_0(X178)
        | ~ v19_lattices(X178,X177)
        | ~ v20_lattices(X178,X177)
        | ~ m1_subset_1(X178,k1_zfmisc_1(u1_struct_0(X177)))
        | v2_struct_0(X177)
        | ~ v10_lattices(X177)
        | ~ v3_filter_0(X177)
        | ~ l3_lattices(X177) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l72_filter_1])])])])])).

fof(c_0_16,plain,(
    ! [X258,X259] :
      ( ~ r2_hidden(X258,X259)
      | ~ v1_xboole_0(X259) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v3_filter_0(esk1_0)
    & l3_lattices(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v19_lattices(esk2_0,esk1_0)
    & v20_lattices(esk2_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk1_0))
    & r2_hidden(esk3_0,k6_eqrel_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_filter_0(esk1_0,esk2_0),esk4_0))
    & r2_hidden(esk5_0,k6_eqrel_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_filter_0(esk1_0,esk2_0),esk4_0))
    & ( ~ r2_hidden(k3_lattices(esk1_0,esk3_0,esk5_0),k6_eqrel_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_filter_0(esk1_0,esk2_0),esk4_0))
      | ~ r2_hidden(k4_lattices(esk1_0,esk3_0,esk5_0),k6_eqrel_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_filter_0(esk1_0,esk2_0),esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X1),u1_struct_0(X1),k9_filter_0(X1,X4),X3))
    | v1_xboole_0(X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(k7_filter_0(X1,X2,X3),X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v19_lattices(X4,X1)
    | ~ v20_lattices(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X101,X102,X103] :
      ( v2_struct_0(X101)
      | ~ v6_lattices(X101)
      | ~ l1_lattices(X101)
      | ~ m1_subset_1(X102,u1_struct_0(X101))
      | ~ m1_subset_1(X103,u1_struct_0(X101))
      | k4_lattices(X101,X102,X103) = k4_lattices(X101,X103,X102) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

fof(c_0_21,plain,(
    ! [X104,X105,X106] :
      ( v2_struct_0(X104)
      | ~ v10_lattices(X104)
      | ~ l3_lattices(X104)
      | ~ m1_subset_1(X105,u1_struct_0(X104))
      | ~ m1_subset_1(X106,u1_struct_0(X104))
      | k7_filter_0(X104,X105,X106) = k4_lattices(X104,k4_filter_0(X104,X105,X106),k4_filter_0(X104,X106,X105)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_filter_0])])])])).

fof(c_0_22,plain,(
    ! [X129,X130,X131] :
      ( v2_struct_0(X129)
      | ~ v10_lattices(X129)
      | ~ l3_lattices(X129)
      | ~ m1_subset_1(X130,u1_struct_0(X129))
      | ~ m1_subset_1(X131,u1_struct_0(X129))
      | m1_subset_1(k4_filter_0(X129,X130,X131),u1_struct_0(X129)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_filter_0])])])).

fof(c_0_23,plain,(
    ! [X24] :
      ( ( ~ v2_struct_0(X24)
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( v4_lattices(X24)
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( v5_lattices(X24)
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( v6_lattices(X24)
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( v7_lattices(X24)
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( v8_lattices(X24)
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( v9_lattices(X24)
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_24,plain,(
    ! [X148] :
      ( ( l1_lattices(X148)
        | ~ l3_lattices(X148) )
      & ( l2_lattices(X148)
        | ~ l3_lattices(X148) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_25,plain,(
    ! [X235,X236] :
      ( v2_struct_0(X235)
      | ~ v6_lattices(X235)
      | ~ v8_lattices(X235)
      | ~ v9_lattices(X235)
      | ~ l3_lattices(X235)
      | ~ m1_subset_1(X236,u1_struct_0(X235))
      | k1_lattices(X235,X236,X236) = X236 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).

fof(c_0_26,plain,(
    ! [X219,X220,X221] :
      ( v2_struct_0(X219)
      | ~ v4_lattices(X219)
      | ~ l2_lattices(X219)
      | ~ m1_subset_1(X220,u1_struct_0(X219))
      | ~ m1_subset_1(X221,u1_struct_0(X219))
      | k3_lattices(X219,X220,X221) = k1_lattices(X219,X220,X221) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(k3_lattices(esk1_0,esk3_0,esk5_0),k6_eqrel_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_filter_0(esk1_0,esk2_0),esk4_0))
    | ~ r2_hidden(k4_lattices(esk1_0,esk3_0,esk5_0),k6_eqrel_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_filter_0(esk1_0,esk2_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k6_eqrel_1(u1_struct_0(X2),u1_struct_0(X2),k9_filter_0(X2,X3),X4))
    | v2_struct_0(X2)
    | ~ r2_hidden(k7_filter_0(X2,X1,X4),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v20_lattices(X3,X2)
    | ~ v19_lattices(X3,X2)
    | ~ l3_lattices(X2)
    | ~ v3_filter_0(X2)
    | ~ v10_lattices(X2) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( v20_lattices(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( v19_lattices(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( v3_filter_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | k7_filter_0(X1,X2,X3) = k4_lattices(X1,k4_filter_0(X1,X2,X3),k4_filter_0(X1,X3,X2))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_42,plain,(
    ! [X248,X249,X250,X251,X252,X253] :
      ( ( r2_hidden(k7_filter_0(X248,k3_lattices(X248,X250,X252),k3_lattices(X248,X251,X253)),X249)
        | ~ r2_hidden(k7_filter_0(X248,X250,X251),X249)
        | ~ r2_hidden(k7_filter_0(X248,X252,X253),X249)
        | ~ m1_subset_1(X253,u1_struct_0(X248))
        | ~ m1_subset_1(X252,u1_struct_0(X248))
        | ~ m1_subset_1(X251,u1_struct_0(X248))
        | ~ m1_subset_1(X250,u1_struct_0(X248))
        | v1_xboole_0(X249)
        | ~ v19_lattices(X249,X248)
        | ~ v20_lattices(X249,X248)
        | ~ m1_subset_1(X249,k1_zfmisc_1(u1_struct_0(X248)))
        | v2_struct_0(X248)
        | ~ v10_lattices(X248)
        | ~ v3_filter_0(X248)
        | ~ l3_lattices(X248) )
      & ( r2_hidden(k7_filter_0(X248,k4_lattices(X248,X250,X252),k4_lattices(X248,X251,X253)),X249)
        | ~ r2_hidden(k7_filter_0(X248,X250,X251),X249)
        | ~ r2_hidden(k7_filter_0(X248,X252,X253),X249)
        | ~ m1_subset_1(X253,u1_struct_0(X248))
        | ~ m1_subset_1(X252,u1_struct_0(X248))
        | ~ m1_subset_1(X251,u1_struct_0(X248))
        | ~ m1_subset_1(X250,u1_struct_0(X248))
        | v1_xboole_0(X249)
        | ~ v19_lattices(X249,X248)
        | ~ v20_lattices(X249,X248)
        | ~ m1_subset_1(X249,k1_zfmisc_1(u1_struct_0(X248)))
        | v2_struct_0(X248)
        | ~ v10_lattices(X248)
        | ~ v3_filter_0(X248)
        | ~ l3_lattices(X248) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_filter_1])])])])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | k1_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(k4_lattices(esk1_0,esk3_0,esk5_0),k6_eqrel_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_filter_0(esk1_0,esk2_0),esk4_0))
    | ~ r2_hidden(k7_filter_0(esk1_0,k3_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_47,plain,
    ( k4_lattices(X1,k4_filter_0(X1,X2,X3),k4_filter_0(X1,X3,X2)) = k7_filter_0(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(k7_filter_0(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X4,X5)),X6)
    | v1_xboole_0(X6)
    | v2_struct_0(X1)
    | ~ r2_hidden(k7_filter_0(X1,X2,X4),X6)
    | ~ r2_hidden(k7_filter_0(X1,X3,X5),X6)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v19_lattices(X6,X1)
    | ~ v20_lattices(X6,X1)
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k3_lattices(X1,X2,X2) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ v4_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_50,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_53,plain,
    ( r2_hidden(k7_filter_0(X2,X1,X4),X3)
    | v1_xboole_0(X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k6_eqrel_1(u1_struct_0(X2),u1_struct_0(X2),k9_filter_0(X2,X3),X4))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v19_lattices(X3,X2)
    | ~ v20_lattices(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v10_lattices(X2)
    | ~ v3_filter_0(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_0,k6_eqrel_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_filter_0(esk1_0,esk2_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_0,k6_eqrel_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_filter_0(esk1_0,esk2_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_59,plain,(
    ! [X237,X238] :
      ( v2_struct_0(X237)
      | ~ v6_lattices(X237)
      | ~ v8_lattices(X237)
      | ~ v9_lattices(X237)
      | ~ l3_lattices(X237)
      | ~ m1_subset_1(X238,u1_struct_0(X237))
      | k4_lattices(X237,X238,X238) = X238 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_lattices])])])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(k7_filter_0(esk1_0,k3_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ r2_hidden(k7_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_61,plain,
    ( k7_filter_0(X1,X2,X3) = k7_filter_0(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_47])).

cnf(c_0_62,plain,
    ( r2_hidden(k7_filter_0(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X4,X5)),X6)
    | v2_struct_0(X1)
    | ~ r2_hidden(k7_filter_0(X1,X3,X5),X6)
    | ~ r2_hidden(k7_filter_0(X1,X2,X4),X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v20_lattices(X6,X1)
    | ~ v19_lattices(X6,X1)
    | ~ l3_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_48,c_0_19])).

cnf(c_0_63,plain,
    ( k3_lattices(X1,X2,X2) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_40]),c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k7_filter_0(esk1_0,esk5_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29]),c_0_30]),c_0_55]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_56]),c_0_36])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k7_filter_0(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_57]),c_0_29]),c_0_30]),c_0_58]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_56]),c_0_36])).

cnf(c_0_66,plain,
    ( r2_hidden(k7_filter_0(X1,k4_lattices(X1,X2,X3),k4_lattices(X1,X4,X5)),X6)
    | v1_xboole_0(X6)
    | v2_struct_0(X1)
    | ~ r2_hidden(k7_filter_0(X1,X2,X4),X6)
    | ~ r2_hidden(k7_filter_0(X1,X3,X5),X6)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v19_lattices(X6,X1)
    | ~ v20_lattices(X6,X1)
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(k7_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k7_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_30]),c_0_33]),c_0_35])]),c_0_36])).

cnf(c_0_69,plain,
    ( r2_hidden(k7_filter_0(X1,X2,k3_lattices(X1,X3,X4)),X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k7_filter_0(X1,X2,X4),X5)
    | ~ r2_hidden(k7_filter_0(X1,X2,X3),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v20_lattices(X5,X1)
    | ~ v19_lattices(X5,X1)
    | ~ l3_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k7_filter_0(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_61]),c_0_30]),c_0_55]),c_0_33]),c_0_35])]),c_0_36])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k7_filter_0(esk1_0,esk4_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_61]),c_0_30]),c_0_58]),c_0_33]),c_0_35])]),c_0_36])).

cnf(c_0_72,plain,
    ( r2_hidden(k7_filter_0(X1,k4_lattices(X1,X2,X3),k4_lattices(X1,X4,X5)),X6)
    | v2_struct_0(X1)
    | ~ r2_hidden(k7_filter_0(X1,X3,X5),X6)
    | ~ r2_hidden(k7_filter_0(X1,X2,X4),X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v20_lattices(X6,X1)
    | ~ v19_lattices(X6,X1)
    | ~ l3_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_66,c_0_19])).

cnf(c_0_73,plain,
    ( k4_lattices(X1,X2,X2) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_50]),c_0_40]),c_0_52])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_hidden(k7_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71]),c_0_29]),c_0_55]),c_0_58]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_75,plain,
    ( r2_hidden(k7_filter_0(X1,k4_lattices(X1,X2,X3),X4),X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k7_filter_0(X1,X3,X4),X5)
    | ~ r2_hidden(k7_filter_0(X1,X2,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v20_lattices(X5,X1)
    | ~ v19_lattices(X5,X1)
    | ~ l3_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ v10_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

fof(c_0_76,plain,(
    ! [X122,X123,X124] :
      ( v2_struct_0(X122)
      | ~ v4_lattices(X122)
      | ~ l2_lattices(X122)
      | ~ m1_subset_1(X123,u1_struct_0(X122))
      | ~ m1_subset_1(X124,u1_struct_0(X122))
      | m1_subset_1(k3_lattices(X122,X123,X124),u1_struct_0(X122)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_lattices])])])).

cnf(c_0_77,negated_conjecture,
    ( ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_64]),c_0_65]),c_0_29]),c_0_30]),c_0_55]),c_0_58]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_79,plain,(
    ! [X132,X133,X134] :
      ( v2_struct_0(X132)
      | ~ v6_lattices(X132)
      | ~ l1_lattices(X132)
      | ~ m1_subset_1(X133,u1_struct_0(X132))
      | ~ m1_subset_1(X134,u1_struct_0(X132))
      | m1_subset_1(k4_lattices(X132,X133,X134),u1_struct_0(X132)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_80,negated_conjecture,
    ( ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_55]),c_0_58])]),c_0_36])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( ~ l1_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_55]),c_0_58])]),c_0_36])).

cnf(c_0_83,negated_conjecture,
    ( ~ l1_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_51]),c_0_33]),c_0_35])]),c_0_36])).

cnf(c_0_84,negated_conjecture,
    ( ~ l1_lattices(esk1_0)
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_40]),c_0_33]),c_0_35])]),c_0_36])).

cnf(c_0_85,negated_conjecture,
    ( ~ l2_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_41]),c_0_33])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_45]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
