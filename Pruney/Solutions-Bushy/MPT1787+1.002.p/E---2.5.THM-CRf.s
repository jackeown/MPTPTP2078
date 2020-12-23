%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1787+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:44 EST 2020

% Result     : Theorem 9.54s
% Output     : CNFRefutation 9.54s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 175 expanded)
%              Number of clauses        :   46 (  71 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  336 ( 665 expanded)
%              Number of equality atoms :   40 (  57 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t102_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r2_hidden(X2,k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(fraenkel_a_2_0_tmap_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_tmap_1(X2,X3))
      <=> ? [X4,X5] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = k4_subset_1(u1_struct_0(X2),X4,k9_subset_1(u1_struct_0(X2),X5,X3))
            & r2_hidden(X4,u1_pre_topc(X2))
            & r2_hidden(X5,u1_pre_topc(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_tmap_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(d8_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k5_tmap_1(X1,X2) = a_2_0_tmap_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tmap_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t5_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_17,plain,(
    ! [X42,X43] :
      ( ~ r1_tarski(X42,X43)
      | k3_xboole_0(X42,X43) = X42 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_18,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_19,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X38))
      | k9_subset_1(X38,X39,X40) = k3_xboole_0(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | m1_subset_1(k9_subset_1(X22,X23,X24),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r2_hidden(X2,k5_tmap_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t102_tmap_1])).

cnf(c_0_26,plain,
    ( k9_subset_1(X1,X2,X3) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X45,X46] :
      ( ( ~ m1_subset_1(X45,k1_zfmisc_1(X46))
        | r1_tarski(X45,X46) )
      & ( ~ r1_tarski(X45,X46)
        | m1_subset_1(X45,k1_zfmisc_1(X46)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v2_pre_topc(esk7_0)
    & l1_pre_topc(esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & ~ r2_hidden(esk8_0,k5_tmap_1(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).

fof(c_0_30,plain,(
    ! [X28,X29,X30,X33,X34] :
      ( ( m1_subset_1(esk5_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( m1_subset_1(esk6_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( X28 = k4_subset_1(u1_struct_0(X29),esk5_3(X28,X29,X30),k9_subset_1(u1_struct_0(X29),esk6_3(X28,X29,X30),X30))
        | ~ r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( r2_hidden(esk5_3(X28,X29,X30),u1_pre_topc(X29))
        | ~ r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( r2_hidden(esk6_3(X28,X29,X30),u1_pre_topc(X29))
        | ~ r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X29)))
        | X28 != k4_subset_1(u1_struct_0(X29),X33,k9_subset_1(u1_struct_0(X29),X34,X30))
        | ~ r2_hidden(X33,u1_pre_topc(X29))
        | ~ r2_hidden(X34,u1_pre_topc(X29))
        | r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_tmap_1])])])])])])).

fof(c_0_31,plain,(
    ! [X47,X48,X49] :
      ( ~ r2_hidden(X47,X48)
      | ~ m1_subset_1(X48,k1_zfmisc_1(X49))
      | m1_subset_1(X47,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_32,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | m1_subset_1(u1_pre_topc(X25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_33,plain,
    ( k9_subset_1(X1,X2,k9_subset_1(X1,X3,X4)) = k9_subset_1(X1,X3,X4)
    | ~ r1_tarski(k9_subset_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(X4,a_2_0_tmap_1(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k4_subset_1(u1_struct_0(X2),X1,k9_subset_1(u1_struct_0(X2),X3,X5))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k9_subset_1(X1,X2,k9_subset_1(X1,X3,X4)) = k9_subset_1(X1,X3,X4)
    | ~ m1_subset_1(k9_subset_1(X1,X3,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),X1,esk8_0) = esk8_0
    | ~ r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_35])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X3,X4)),a_2_0_tmap_1(X1,X4))
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),X1,esk8_0) = esk8_0
    | ~ r1_tarski(esk8_0,X2)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_35])])).

fof(c_0_44,plain,(
    ! [X44] : k3_xboole_0(X44,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X3,X4)),a_2_0_tmap_1(X1,X4))
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_41,c_0_42]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_49,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
      | k4_subset_1(X35,X36,X37) = k2_xboole_0(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_50,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0) = esk8_0
    | ~ r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_35])).

fof(c_0_51,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r1_tarski(X14,u1_pre_topc(X13))
        | r2_hidden(k5_setfam_1(u1_struct_0(X13),X14),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(X15,u1_pre_topc(X13))
        | ~ r2_hidden(X16,u1_pre_topc(X13))
        | r2_hidden(k9_subset_1(u1_struct_0(X13),X15,X16),u1_pre_topc(X13))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk2_1(X13),u1_pre_topc(X13))
        | m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk3_1(X13),u1_pre_topc(X13))
        | m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk2_1(X13),esk3_1(X13)),u1_pre_topc(X13))
        | m1_subset_1(esk1_1(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | r1_tarski(esk1_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | r1_tarski(esk1_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk2_1(X13),u1_pre_topc(X13))
        | r1_tarski(esk1_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk3_1(X13),u1_pre_topc(X13))
        | r1_tarski(esk1_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk2_1(X13),esk3_1(X13)),u1_pre_topc(X13))
        | r1_tarski(esk1_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_1(X13),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk2_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk3_1(X13),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X13),esk2_1(X13),esk3_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X13),esk1_1(X13)),u1_pre_topc(X13))
        | ~ r2_hidden(u1_struct_0(X13),u1_pre_topc(X13))
        | v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | k5_tmap_1(X20,X21) = a_2_0_tmap_1(X20,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tmap_1])])])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_subset_1(u1_struct_0(esk7_0),X1,k9_subset_1(u1_struct_0(esk7_0),X2,esk8_0)),a_2_0_tmap_1(esk7_0,esk8_0))
    | ~ r2_hidden(X2,u1_pre_topc(esk7_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_35]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_55,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0) = esk8_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_34])).

cnf(c_0_57,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_58,plain,(
    ! [X41] : k2_xboole_0(X41,k1_xboole_0) = X41 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_59,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_60,plain,(
    ! [X50] :
      ( ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | r2_hidden(k1_xboole_0,u1_pre_topc(X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_pre_topc])])).

cnf(c_0_61,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_21])).

fof(c_0_63,plain,(
    ! [X26] : m1_subset_1(esk4_1(X26),X26) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | k5_tmap_1(X1,X2) = a_2_0_tmap_1(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k2_xboole_0(X1,k9_subset_1(u1_struct_0(esk7_0),X2,esk8_0)),a_2_0_tmap_1(esk7_0,esk8_0))
    | ~ r2_hidden(X2,u1_pre_topc(esk7_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk7_0))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk7_0),X2,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),u1_struct_0(esk7_0),esk8_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_46]),c_0_47])])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k5_tmap_1(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_74,negated_conjecture,
    ( k5_tmap_1(esk7_0,esk8_0) = a_2_0_tmap_1(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_35]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k2_xboole_0(X1,esk8_0),a_2_0_tmap_1(esk7_0,esk8_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_35])])).

cnf(c_0_76,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_46]),c_0_47])])).

cnf(c_0_78,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk8_0,a_2_0_tmap_1(esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78])]),c_0_79]),
    [proof]).

%------------------------------------------------------------------------------
