%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t6_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:17 EDT 2019

% Result     : Theorem 21.79s
% Output     : CNFRefutation 21.79s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 268 expanded)
%              Number of clauses        :   48 (  96 expanded)
%              Number of leaves         :   14 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  450 (2755 expanded)
%              Number of equality atoms :   76 ( 453 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_tmap_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(X1)) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ( r1_subset_1(X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                           => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                              & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3) = X5
                              & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4) = X6 ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',t6_tmap_1)).

fof(d1_tmap_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(X1)) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,X4,X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                         => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2)
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))) )
                               => ( X7 = k1_tmap_1(X1,X2,X3,X4,X5,X6)
                                <=> ( k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3) = X5
                                    & k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4) = X6 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',d1_tmap_1)).

fof(dt_k1_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X3,k1_zfmisc_1(X1))
        & ~ v1_xboole_0(X4)
        & m1_subset_1(X4,k1_zfmisc_1(X1))
        & v1_funct_1(X5)
        & v1_funct_2(X5,X3,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X4,X2)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
     => ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
        & v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
        & m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',dt_k1_tmap_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',d7_xboole_0)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',redefinition_r1_subset_1)).

fof(symmetry_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
       => r1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',symmetry_r1_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',t6_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',commutativity_k3_xboole_0)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',cc3_relset_1)).

fof(t38_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',t38_funct_2)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',t17_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',t2_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',dt_o_0_0_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t6_tmap_1.p',redefinition_k9_subset_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X1)) )
               => ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                   => ( r1_subset_1(X3,X4)
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,X3,X2)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,X4,X2)
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                             => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                                & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3) = X5
                                & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4) = X6 ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tmap_1])).

fof(c_0_15,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32] :
      ( ( k2_partfun1(k4_subset_1(X26,X28,X29),X27,X32,X28) = X30
        | X32 != k1_tmap_1(X26,X27,X28,X29,X30,X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,k4_subset_1(X26,X28,X29),X27)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X26,X28,X29),X27)))
        | k2_partfun1(X28,X27,X30,k9_subset_1(X26,X28,X29)) != k2_partfun1(X29,X27,X31,k9_subset_1(X26,X28,X29))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X27)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X27)))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X27)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X27)))
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(X26))
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | v1_xboole_0(X27)
        | v1_xboole_0(X26) )
      & ( k2_partfun1(k4_subset_1(X26,X28,X29),X27,X32,X29) = X31
        | X32 != k1_tmap_1(X26,X27,X28,X29,X30,X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,k4_subset_1(X26,X28,X29),X27)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X26,X28,X29),X27)))
        | k2_partfun1(X28,X27,X30,k9_subset_1(X26,X28,X29)) != k2_partfun1(X29,X27,X31,k9_subset_1(X26,X28,X29))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X27)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X27)))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X27)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X27)))
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(X26))
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | v1_xboole_0(X27)
        | v1_xboole_0(X26) )
      & ( k2_partfun1(k4_subset_1(X26,X28,X29),X27,X32,X28) != X30
        | k2_partfun1(k4_subset_1(X26,X28,X29),X27,X32,X29) != X31
        | X32 = k1_tmap_1(X26,X27,X28,X29,X30,X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,k4_subset_1(X26,X28,X29),X27)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X26,X28,X29),X27)))
        | k2_partfun1(X28,X27,X30,k9_subset_1(X26,X28,X29)) != k2_partfun1(X29,X27,X31,k9_subset_1(X26,X28,X29))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X27)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X27)))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X27)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X27)))
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(X26))
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | v1_xboole_0(X27)
        | v1_xboole_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_16,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( v1_funct_1(k1_tmap_1(X35,X36,X37,X38,X39,X40))
        | v1_xboole_0(X35)
        | v1_xboole_0(X36)
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
        | v1_xboole_0(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(X35))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X36)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X36)))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X36)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X36))) )
      & ( v1_funct_2(k1_tmap_1(X35,X36,X37,X38,X39,X40),k4_subset_1(X35,X37,X38),X36)
        | v1_xboole_0(X35)
        | v1_xboole_0(X36)
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
        | v1_xboole_0(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(X35))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X36)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X36)))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X36)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X36))) )
      & ( m1_subset_1(k1_tmap_1(X35,X36,X37,X38,X39,X40),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X35,X37,X38),X36)))
        | v1_xboole_0(X35)
        | v1_xboole_0(X36)
        | v1_xboole_0(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
        | v1_xboole_0(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(X35))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X36)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X36)))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X36)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_17,plain,(
    ! [X33,X34] :
      ( ( ~ r1_xboole_0(X33,X34)
        | k3_xboole_0(X33,X34) = k1_xboole_0 )
      & ( k3_xboole_0(X33,X34) != k1_xboole_0
        | r1_xboole_0(X33,X34) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_18,plain,(
    ! [X75,X76] :
      ( ( ~ r1_subset_1(X75,X76)
        | r1_xboole_0(X75,X76)
        | v1_xboole_0(X75)
        | v1_xboole_0(X76) )
      & ( ~ r1_xboole_0(X75,X76)
        | r1_subset_1(X75,X76)
        | v1_xboole_0(X75)
        | v1_xboole_0(X76) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

fof(c_0_19,plain,(
    ! [X85,X86] :
      ( v1_xboole_0(X85)
      | v1_xboole_0(X86)
      | ~ r1_subset_1(X85,X86)
      | r1_subset_1(X86,X85) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[symmetry_r1_subset_1])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ~ v1_xboole_0(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
    & r1_subset_1(esk3_0,esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))
    & ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
      | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
      | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_21,plain,(
    ! [X113] :
      ( ~ v1_xboole_0(X113)
      | X113 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_22,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | X5 != k1_tmap_1(X1,X4,X2,X3,X7,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X2,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_subset_1(X2,X1)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r1_subset_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_32,plain,(
    ! [X18,X19] : k3_xboole_0(X18,X19) = k3_xboole_0(X19,X18) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_33,plain,(
    ! [X118,X119,X120] :
      ( ~ v1_xboole_0(X118)
      | ~ m1_subset_1(X120,k1_zfmisc_1(k2_zfmisc_1(X118,X119)))
      | v1_xboole_0(X120) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

fof(c_0_34,plain,(
    ! [X101,X102,X103,X104] :
      ( ( v1_funct_1(k2_partfun1(X101,X102,X104,X103))
        | X102 = k1_xboole_0
        | ~ r1_tarski(X103,X101)
        | ~ v1_funct_1(X104)
        | ~ v1_funct_2(X104,X101,X102)
        | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X101,X102))) )
      & ( v1_funct_2(k2_partfun1(X101,X102,X104,X103),X103,X102)
        | X102 = k1_xboole_0
        | ~ r1_tarski(X103,X101)
        | ~ v1_funct_1(X104)
        | ~ v1_funct_2(X104,X101,X102)
        | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X101,X102))) )
      & ( m1_subset_1(k2_partfun1(X101,X102,X104,X103),k1_zfmisc_1(k2_zfmisc_1(X103,X102)))
        | X102 = k1_xboole_0
        | ~ r1_tarski(X103,X101)
        | ~ v1_funct_1(X104)
        | ~ v1_funct_2(X104,X101,X102)
        | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X101,X102))) )
      & ( v1_funct_1(k2_partfun1(X101,X102,X104,X103))
        | X101 != k1_xboole_0
        | ~ r1_tarski(X103,X101)
        | ~ v1_funct_1(X104)
        | ~ v1_funct_2(X104,X101,X102)
        | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X101,X102))) )
      & ( v1_funct_2(k2_partfun1(X101,X102,X104,X103),X103,X102)
        | X101 != k1_xboole_0
        | ~ r1_tarski(X103,X101)
        | ~ v1_funct_1(X104)
        | ~ v1_funct_2(X104,X101,X102)
        | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X101,X102))) )
      & ( m1_subset_1(k2_partfun1(X101,X102,X104,X103),k1_zfmisc_1(k2_zfmisc_1(X103,X102)))
        | X101 != k1_xboole_0
        | ~ r1_tarski(X103,X101)
        | ~ v1_funct_1(X104)
        | ~ v1_funct_2(X104,X101,X102)
        | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X101,X102))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_2])])])).

fof(c_0_35,plain,(
    ! [X93,X94] : r1_tarski(k3_xboole_0(X93,X94),X93) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_36,plain,(
    ! [X98] : k3_xboole_0(X98,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_39,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3) = X6
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_51,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | X5 != k1_tmap_1(X1,X4,X2,X3,X6,X7)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X3,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X2,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_52,plain,(
    ! [X72,X73,X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(X72))
      | k9_subset_1(X72,X73,X74) = k3_xboole_0(X73,X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( r1_subset_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | X2 = k1_xboole_0
    | ~ r1_tarski(X4,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_60,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48])]),c_0_49]),c_0_31]),c_0_30]),c_0_50])).

cnf(c_0_62,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_63,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_30]),c_0_31]),c_0_55])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | v1_xboole_0(k2_partfun1(X2,X1,X3,X4))
    | ~ r1_tarski(X4,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_xboole_0(X4) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_42]),c_0_41]),c_0_44]),c_0_43]),c_0_46]),c_0_45]),c_0_47]),c_0_48])]),c_0_49]),c_0_31]),c_0_30]),c_0_50])).

cnf(c_0_69,negated_conjecture,
    ( k9_subset_1(X1,esk3_0,esk4_0) = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | v1_xboole_0(k2_partfun1(X2,X1,X3,k1_xboole_0))
    | ~ v1_funct_2(X3,X2,X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_71,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0) != k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_47])])).

cnf(c_0_72,plain,
    ( k2_partfun1(X1,X2,X3,k1_xboole_0) = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_42]),c_0_44]),c_0_46])])).

cnf(c_0_74,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_72]),c_0_41]),c_0_43]),c_0_45])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_74]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
