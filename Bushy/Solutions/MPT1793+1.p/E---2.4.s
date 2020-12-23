%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t109_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:03 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 342 expanded)
%              Number of clauses        :   55 ( 122 expanded)
%              Number of leaves         :   19 (  85 expanded)
%              Depth                    :   17
%              Number of atoms          :  387 (1986 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t109_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_xboole_0(u1_struct_0(X3),X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',t109_tmap_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',t3_subset)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',t35_borsuk_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',fc2_struct_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',dt_m1_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',t4_subset)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',dt_l1_pre_topc)).

fof(t64_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( ( X5 = X6
                              & r1_tmap_1(X2,X1,X3,X5) )
                           => r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',t64_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',dt_k7_tmap_1)).

fof(t108_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ~ r2_hidden(X3,X2)
               => r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',t108_tmap_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',d4_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',commutativity_k3_xboole_0)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',fc4_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',dt_k6_tmap_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',dt_o_0_0_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t109_tmap_1.p',t7_boole)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r1_xboole_0(u1_struct_0(X3),X2)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X3))
                     => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t109_tmap_1])).

fof(c_0_20,plain,(
    ! [X117,X118] :
      ( ( ~ m1_subset_1(X117,k1_zfmisc_1(X118))
        | r1_tarski(X117,X118) )
      & ( ~ r1_tarski(X117,X118)
        | m1_subset_1(X117,k1_zfmisc_1(X118)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,plain,(
    ! [X115,X116] :
      ( ~ l1_pre_topc(X115)
      | ~ m1_pre_topc(X116,X115)
      | r1_tarski(u1_struct_0(X116),u1_struct_0(X115)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_22,plain,(
    ! [X110,X111] :
      ( ~ m1_subset_1(X110,X111)
      | v1_xboole_0(X111)
      | r2_hidden(X110,X111) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & r1_xboole_0(u1_struct_0(esk3_0),esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ~ r1_tmap_1(esk3_0,k6_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X138] :
      ( v2_struct_0(X138)
      | ~ l1_struct_0(X138)
      | ~ v1_xboole_0(u1_struct_0(X138)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X62,X63] :
      ( ~ l1_pre_topc(X62)
      | ~ m1_pre_topc(X63,X62)
      | l1_pre_topc(X63) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_30,plain,(
    ! [X119,X120,X121] :
      ( ~ r2_hidden(X119,X120)
      | ~ m1_subset_1(X120,k1_zfmisc_1(X121))
      | m1_subset_1(X119,X121) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_31,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | r2_hidden(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_37,plain,(
    ! [X61] :
      ( ~ l1_pre_topc(X61)
      | l1_struct_0(X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_38,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,plain,(
    ! [X125,X126,X127,X128,X129,X130] :
      ( v2_struct_0(X125)
      | ~ v2_pre_topc(X125)
      | ~ l1_pre_topc(X125)
      | v2_struct_0(X126)
      | ~ v2_pre_topc(X126)
      | ~ l1_pre_topc(X126)
      | ~ v1_funct_1(X127)
      | ~ v1_funct_2(X127,u1_struct_0(X126),u1_struct_0(X125))
      | ~ m1_subset_1(X127,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X126),u1_struct_0(X125))))
      | v2_struct_0(X128)
      | ~ m1_pre_topc(X128,X126)
      | ~ m1_subset_1(X129,u1_struct_0(X126))
      | ~ m1_subset_1(X130,u1_struct_0(X128))
      | X129 != X130
      | ~ r1_tmap_1(X126,X125,X127,X129)
      | r1_tmap_1(X128,X125,k2_tmap_1(X126,X125,X127,X128),X130) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_43,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_33])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | X5 != X6
    | ~ r1_tmap_1(X2,X1,X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,k6_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_53,plain,(
    ! [X56,X57] :
      ( ( v1_funct_1(k7_tmap_1(X56,X57))
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56))) )
      & ( v1_funct_2(k7_tmap_1(X56,X57),u1_struct_0(X56),u1_struct_0(k6_tmap_1(X56,X57)))
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56))) )
      & ( m1_subset_1(k7_tmap_1(X56,X57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(k6_tmap_1(X56,X57)))))
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_54,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ v1_funct_2(k7_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0))
    | ~ r1_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk4_0)
    | ~ m1_subset_1(k7_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))))
    | ~ l1_pre_topc(k6_tmap_1(esk1_0,esk2_0))
    | ~ v2_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_32]),c_0_28]),c_0_33]),c_0_50])]),c_0_36]),c_0_51]),c_0_52])])).

cnf(c_0_55,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0))
    | ~ r1_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk4_0)
    | ~ m1_subset_1(k7_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(k6_tmap_1(esk1_0,esk2_0)))))
    | ~ l1_pre_topc(k6_tmap_1(esk1_0,esk2_0))
    | ~ v2_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_33]),c_0_50])]),c_0_51])).

cnf(c_0_58,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_59,plain,(
    ! [X103,X104,X105] :
      ( v2_struct_0(X103)
      | ~ v2_pre_topc(X103)
      | ~ l1_pre_topc(X103)
      | ~ m1_subset_1(X104,k1_zfmisc_1(u1_struct_0(X103)))
      | ~ m1_subset_1(X105,u1_struct_0(X103))
      | r2_hidden(X105,X104)
      | r1_tmap_1(X103,k6_tmap_1(X103,X104),k7_tmap_1(X103,X104),X105) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t108_tmap_1])])])])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0))
    | ~ r1_tmap_1(esk1_0,k6_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,esk2_0),esk4_0)
    | ~ l1_pre_topc(k6_tmap_1(esk1_0,esk2_0))
    | ~ v2_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_56]),c_0_33]),c_0_50])]),c_0_51])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_62,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( r2_hidden(X27,X24)
        | ~ r2_hidden(X27,X26)
        | X26 != k3_xboole_0(X24,X25) )
      & ( r2_hidden(X27,X25)
        | ~ r2_hidden(X27,X26)
        | X26 != k3_xboole_0(X24,X25) )
      & ( ~ r2_hidden(X28,X24)
        | ~ r2_hidden(X28,X25)
        | r2_hidden(X28,X26)
        | X26 != k3_xboole_0(X24,X25) )
      & ( ~ r2_hidden(esk5_3(X29,X30,X31),X31)
        | ~ r2_hidden(esk5_3(X29,X30,X31),X29)
        | ~ r2_hidden(esk5_3(X29,X30,X31),X30)
        | X31 = k3_xboole_0(X29,X30) )
      & ( r2_hidden(esk5_3(X29,X30,X31),X29)
        | r2_hidden(esk5_3(X29,X30,X31),X31)
        | X31 = k3_xboole_0(X29,X30) )
      & ( r2_hidden(esk5_3(X29,X30,X31),X30)
        | r2_hidden(esk5_3(X29,X30,X31),X31)
        | X31 = k3_xboole_0(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_63,plain,(
    ! [X33,X34] :
      ( ( ~ r1_xboole_0(X33,X34)
        | k3_xboole_0(X33,X34) = k1_xboole_0 )
      & ( k3_xboole_0(X33,X34) != k1_xboole_0
        | r1_xboole_0(X33,X34) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_64,plain,(
    ! [X16,X17] : k3_xboole_0(X16,X17) = k3_xboole_0(X17,X16) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_65,plain,(
    ! [X139,X140] :
      ( ( ~ v2_struct_0(k6_tmap_1(X139,X140))
        | v2_struct_0(X139)
        | ~ v2_pre_topc(X139)
        | ~ l1_pre_topc(X139)
        | ~ m1_subset_1(X140,k1_zfmisc_1(u1_struct_0(X139))) )
      & ( v1_pre_topc(k6_tmap_1(X139,X140))
        | v2_struct_0(X139)
        | ~ v2_pre_topc(X139)
        | ~ l1_pre_topc(X139)
        | ~ m1_subset_1(X140,k1_zfmisc_1(u1_struct_0(X139))) )
      & ( v2_pre_topc(k6_tmap_1(X139,X140))
        | v2_struct_0(X139)
        | ~ v2_pre_topc(X139)
        | ~ l1_pre_topc(X139)
        | ~ m1_subset_1(X140,k1_zfmisc_1(u1_struct_0(X139))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | v2_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k7_tmap_1(esk1_0,esk2_0))
    | ~ l1_pre_topc(k6_tmap_1(esk1_0,esk2_0))
    | ~ v2_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_56]),c_0_52]),c_0_33]),c_0_50])]),c_0_51])).

cnf(c_0_67,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | v2_struct_0(k6_tmap_1(esk1_0,esk2_0))
    | ~ l1_pre_topc(k6_tmap_1(esk1_0,esk2_0))
    | ~ v2_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_56]),c_0_33]),c_0_50])]),c_0_51])).

fof(c_0_74,plain,(
    ! [X52,X53] :
      ( ( v1_pre_topc(k6_tmap_1(X52,X53))
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52))) )
      & ( v2_pre_topc(k6_tmap_1(X52,X53))
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52))) )
      & ( l1_pre_topc(k6_tmap_1(X52,X53))
        | v2_struct_0(X52)
        | ~ v2_pre_topc(X52)
        | ~ l1_pre_topc(X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(esk2_0,u1_struct_0(esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | ~ l1_pre_topc(k6_tmap_1(esk1_0,esk2_0))
    | ~ v2_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_56]),c_0_33]),c_0_50])]),c_0_51])).

cnf(c_0_78,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_79,plain,(
    ! [X131] :
      ( ~ v1_xboole_0(X131)
      | X131 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | ~ l1_pre_topc(k6_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_56]),c_0_33]),c_0_50])]),c_0_51])).

cnf(c_0_82,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_84,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_85,plain,(
    ! [X132,X133] :
      ( ~ r2_hidden(X132,X133)
      | ~ v1_xboole_0(X133) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk4_0,k1_xboole_0)
    | ~ r2_hidden(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_47])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_56]),c_0_33]),c_0_50])]),c_0_51])).

cnf(c_0_88,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_91,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
