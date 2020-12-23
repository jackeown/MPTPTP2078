%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t12_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:27 EDT 2019

% Result     : Theorem 157.61s
% Output     : CNFRefutation 157.61s
% Verified   : 
% Statistics : Number of formulae       :  113 (25498 expanded)
%              Number of clauses        :   92 (10834 expanded)
%              Number of leaves         :   10 (5881 expanded)
%              Depth                    :   20
%              Number of atoms          :  404 (89274 expanded)
%              Number of equality atoms :   45 (25784 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v2_pre_topc(X1) )
           => v2_pre_topc(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t12_tex_2.p',t12_tex_2)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t12_tex_2.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t12_tex_2.p',dt_u1_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t12_tex_2.p',dt_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t12_tex_2.p',abstractness_v1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/tex_2__t12_tex_2.p',d1_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t12_tex_2.p',t4_subset)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t12_tex_2.p',fc6_pre_topc)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t12_tex_2.p',redefinition_k9_subset_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t12_tex_2.p',redefinition_k5_setfam_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v2_pre_topc(X1) )
             => v2_pre_topc(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_tex_2])).

fof(c_0_11,plain,(
    ! [X149,X150,X151,X152] :
      ( ( X149 = X151
        | g1_pre_topc(X149,X150) != g1_pre_topc(X151,X152)
        | ~ m1_subset_1(X150,k1_zfmisc_1(k1_zfmisc_1(X149))) )
      & ( X150 = X152
        | g1_pre_topc(X149,X150) != g1_pre_topc(X151,X152)
        | ~ m1_subset_1(X150,k1_zfmisc_1(k1_zfmisc_1(X149))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & v2_pre_topc(esk1_0)
    & ~ v2_pre_topc(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_13,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( u1_pre_topc(esk2_0) = X1
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(X2,X1)
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_16,plain,(
    ! [X123] :
      ( ~ l1_pre_topc(X123)
      | m1_subset_1(u1_pre_topc(X123),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X123)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_17,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk1_0)
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X115,X116] :
      ( ( v1_pre_topc(g1_pre_topc(X115,X116))
        | ~ m1_subset_1(X116,k1_zfmisc_1(k1_zfmisc_1(X115))) )
      & ( l1_pre_topc(g1_pre_topc(X115,X116))
        | ~ m1_subset_1(X116,k1_zfmisc_1(k1_zfmisc_1(X115))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_21,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_22,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( u1_pre_topc(esk1_0) = X1
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(X2,X1)
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_21]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_21]),c_0_19])])).

fof(c_0_26,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | ~ v1_pre_topc(X7)
      | X7 = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_27,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_29,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( u1_pre_topc(esk1_0) = X1
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_32,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_25])])).

cnf(c_0_36,negated_conjecture,
    ( u1_pre_topc(esk1_0) = u1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != X1
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_25])])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_25])])).

fof(c_0_39,plain,(
    ! [X108,X109,X110,X111] :
      ( ( r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | ~ v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( ~ m1_subset_1(X109,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X108))))
        | ~ r1_tarski(X109,u1_pre_topc(X108))
        | r2_hidden(k5_setfam_1(u1_struct_0(X108),X109),u1_pre_topc(X108))
        | ~ v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( ~ m1_subset_1(X110,k1_zfmisc_1(u1_struct_0(X108)))
        | ~ m1_subset_1(X111,k1_zfmisc_1(u1_struct_0(X108)))
        | ~ r2_hidden(X110,u1_pre_topc(X108))
        | ~ r2_hidden(X111,u1_pre_topc(X108))
        | r2_hidden(k9_subset_1(u1_struct_0(X108),X110,X111),u1_pre_topc(X108))
        | ~ v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( m1_subset_1(esk4_1(X108),k1_zfmisc_1(u1_struct_0(X108)))
        | m1_subset_1(esk3_1(X108),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X108))))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( m1_subset_1(esk5_1(X108),k1_zfmisc_1(u1_struct_0(X108)))
        | m1_subset_1(esk3_1(X108),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X108))))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( r2_hidden(esk4_1(X108),u1_pre_topc(X108))
        | m1_subset_1(esk3_1(X108),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X108))))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( r2_hidden(esk5_1(X108),u1_pre_topc(X108))
        | m1_subset_1(esk3_1(X108),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X108))))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X108),esk4_1(X108),esk5_1(X108)),u1_pre_topc(X108))
        | m1_subset_1(esk3_1(X108),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X108))))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( m1_subset_1(esk4_1(X108),k1_zfmisc_1(u1_struct_0(X108)))
        | r1_tarski(esk3_1(X108),u1_pre_topc(X108))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( m1_subset_1(esk5_1(X108),k1_zfmisc_1(u1_struct_0(X108)))
        | r1_tarski(esk3_1(X108),u1_pre_topc(X108))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( r2_hidden(esk4_1(X108),u1_pre_topc(X108))
        | r1_tarski(esk3_1(X108),u1_pre_topc(X108))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( r2_hidden(esk5_1(X108),u1_pre_topc(X108))
        | r1_tarski(esk3_1(X108),u1_pre_topc(X108))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X108),esk4_1(X108),esk5_1(X108)),u1_pre_topc(X108))
        | r1_tarski(esk3_1(X108),u1_pre_topc(X108))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( m1_subset_1(esk4_1(X108),k1_zfmisc_1(u1_struct_0(X108)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X108),esk3_1(X108)),u1_pre_topc(X108))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( m1_subset_1(esk5_1(X108),k1_zfmisc_1(u1_struct_0(X108)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X108),esk3_1(X108)),u1_pre_topc(X108))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( r2_hidden(esk4_1(X108),u1_pre_topc(X108))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X108),esk3_1(X108)),u1_pre_topc(X108))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( r2_hidden(esk5_1(X108),u1_pre_topc(X108))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X108),esk3_1(X108)),u1_pre_topc(X108))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X108),esk4_1(X108),esk5_1(X108)),u1_pre_topc(X108))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X108),esk3_1(X108)),u1_pre_topc(X108))
        | ~ r2_hidden(u1_struct_0(X108),u1_pre_topc(X108))
        | v2_pre_topc(X108)
        | ~ l1_pre_topc(X108) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk1_0) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = u1_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_42,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_41]),c_0_37]),c_0_38])])).

fof(c_0_45,plain,(
    ! [X252,X253,X254] :
      ( ~ r2_hidden(X252,X253)
      | ~ m1_subset_1(X253,k1_zfmisc_1(X254))
      | m1_subset_1(X252,X254) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_pre_topc(esk1_0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_38])])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_48,plain,(
    ! [X138] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X138),u1_pre_topc(X138)))
        | ~ v2_pre_topc(X138)
        | ~ l1_pre_topc(X138) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X138),u1_pre_topc(X138)))
        | ~ v2_pre_topc(X138)
        | ~ l1_pre_topc(X138) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( r2_hidden(esk5_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,plain,
    ( r2_hidden(esk5_1(X1),u1_pre_topc(X1))
    | m1_subset_1(esk3_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,plain,
    ( r2_hidden(esk5_1(X1),u1_pre_topc(X1))
    | r1_tarski(esk3_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_58,plain,
    ( r2_hidden(esk4_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_59,plain,
    ( r2_hidden(esk4_1(X1),u1_pre_topc(X1))
    | m1_subset_1(esk3_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_60,plain,
    ( r2_hidden(esk4_1(X1),u1_pre_topc(X1))
    | r1_tarski(esk3_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_61,plain,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_62,plain,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(esk3_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_63,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk4_1(X1),esk5_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_25])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk5_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(esk2_0),esk3_1(esk2_0)),u1_pre_topc(esk1_0))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | r2_hidden(esk5_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk3_1(esk2_0),u1_pre_topc(esk1_0))
    | r2_hidden(esk5_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk4_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(esk2_0),esk3_1(esk2_0)),u1_pre_topc(esk1_0))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | r2_hidden(esk4_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk3_1(esk2_0),u1_pre_topc(esk1_0))
    | r2_hidden(esk4_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_72,plain,
    ( r1_tarski(esk3_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk4_1(X1),esk5_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_73,plain,(
    ! [X242,X243,X244] :
      ( ~ m1_subset_1(X244,k1_zfmisc_1(X242))
      | k9_subset_1(X242,X243,X244) = k3_xboole_0(X243,X244) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk5_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(esk2_0),esk3_1(esk2_0)),u1_pre_topc(esk1_0))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_75,plain,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(esk3_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk3_1(esk2_0),u1_pre_topc(esk1_0))
    | m1_subset_1(esk5_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_77,plain,
    ( v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk4_1(X1),esk5_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_78,plain,(
    ! [X240,X241] :
      ( ~ m1_subset_1(X241,k1_zfmisc_1(k1_zfmisc_1(X240)))
      | k5_setfam_1(X240,X241) = k3_tarski(X241) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(esk2_0),esk4_1(esk2_0),esk5_1(esk2_0)),u1_pre_topc(esk1_0))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_80,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X2),X1,X3),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_40])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk5_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(esk1_0),esk3_1(esk2_0)),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_40]),c_0_40]),c_0_66])])).

cnf(c_0_83,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | r2_hidden(esk5_1(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_40]),c_0_40]),c_0_66])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk3_1(esk2_0),u1_pre_topc(esk1_0))
    | r2_hidden(esk5_1(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_40]),c_0_66])])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk4_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(esk1_0),esk3_1(esk2_0)),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_40]),c_0_40]),c_0_66])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | r2_hidden(esk4_1(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_40]),c_0_40]),c_0_66])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk3_1(esk2_0),u1_pre_topc(esk1_0))
    | r2_hidden(esk4_1(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_40]),c_0_66])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk3_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(esk2_0),esk4_1(esk2_0),esk5_1(esk2_0)),u1_pre_topc(esk1_0))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_90,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk5_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(esk1_0),esk3_1(esk2_0)),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_40]),c_0_40]),c_0_40]),c_0_66])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | m1_subset_1(esk5_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_40]),c_0_21]),c_0_19])]),c_0_51]),c_0_66])])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk3_1(esk2_0),u1_pre_topc(esk1_0))
    | m1_subset_1(esk5_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_40]),c_0_40]),c_0_66])])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk2_0),esk4_1(esk2_0),esk5_1(esk2_0)),u1_pre_topc(esk1_0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(esk2_0),esk3_1(esk2_0)),u1_pre_topc(esk1_0))
    | ~ r2_hidden(u1_struct_0(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_21]),c_0_19])]),c_0_51])).

cnf(c_0_95,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(esk1_0),esk4_1(esk2_0),esk5_1(esk2_0)),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_40]),c_0_40]),c_0_40]),c_0_66])])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk1_0),X1,X2),u1_pre_topc(esk1_0))
    | ~ r2_hidden(X2,u1_pre_topc(esk1_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk1_0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_41]),c_0_38])]),c_0_47]),c_0_47]),c_0_47]),c_0_81]),c_0_81])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk5_1(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_54]),c_0_55])]),c_0_84]),c_0_85])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk4_1(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_83]),c_0_54]),c_0_55])]),c_0_87]),c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(esk3_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(esk1_0),esk4_1(esk2_0),esk5_1(esk2_0)),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_40]),c_0_40]),c_0_66])])).

cnf(c_0_101,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_90])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(esk5_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_83]),c_0_54]),c_0_55])]),c_0_92]),c_0_93])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk1_0),esk4_1(esk2_0),esk5_1(esk2_0)),u1_pre_topc(esk1_0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(esk1_0),esk3_1(esk2_0)),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_40]),c_0_40]),c_0_40]),c_0_66])])).

cnf(c_0_104,plain,
    ( k5_setfam_1(X1,X2) = k5_setfam_1(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_95])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_99])])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(esk3_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ m1_subset_1(esk5_1(esk2_0),k1_zfmisc_1(X1))
    | ~ r2_hidden(k9_subset_1(X1,esk4_1(esk2_0),esk5_1(esk2_0)),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk1_0),esk3_1(esk2_0)),u1_pre_topc(esk1_0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_97]),c_0_98]),c_0_99])])).

cnf(c_0_108,plain,
    ( r2_hidden(k5_setfam_1(X1,X2),u1_pre_topc(X3))
    | ~ r1_tarski(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_83,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(esk3_1(esk2_0),u1_pre_topc(esk1_0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_97]),c_0_102]),c_0_98]),c_0_99])])).

cnf(c_0_111,negated_conjecture,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_54]),c_0_55])]),c_0_109])]),c_0_110])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_53]),c_0_54]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
