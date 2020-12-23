%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:07 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  52 expanded)
%              Number of leaves         :   52 (  52 expanded)
%              Depth                    :    0
%              Number of atoms          :  326 ( 326 expanded)
%              Number of equality atoms :   62 (  62 expanded)
%              Maximal formula depth    :   13 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u439,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X1,X0)
          | u1_pre_topc(sK0) = X0 )
    | ! [X1,X0] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X1,X0)
        | u1_pre_topc(sK0) = X0 ) )).

tff(u438,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | u1_struct_0(sK0) = X0 )
    | ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK0) = X0 ) )).

tff(u437,negated_conjecture,
    ( ~ ! [X5,X4] :
          ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X5,X4)
          | u1_pre_topc(sK2) = X4 )
    | ! [X5,X4] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X5,X4)
        | u1_pre_topc(sK2) = X4 ) )).

tff(u436,negated_conjecture,
    ( ~ ! [X5,X4] :
          ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X4,X5)
          | u1_struct_0(sK2) = X4 )
    | ! [X5,X4] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X4,X5)
        | u1_struct_0(sK2) = X4 ) )).

tff(u435,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( sK4(X0,sK1) != k9_subset_1(u1_struct_0(sK0),X1,k2_struct_0(sK1))
          | ~ r2_hidden(sK4(X0,sK1),u1_pre_topc(sK0))
          | ~ r2_hidden(X1,u1_pre_topc(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | m1_pre_topc(sK1,X0)
          | ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(X0))
          | ~ l1_pre_topc(X0) )
    | ! [X1,X0] :
        ( sK4(X0,sK1) != k9_subset_1(u1_struct_0(sK0),X1,k2_struct_0(sK1))
        | ~ r2_hidden(sK4(X0,sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(X1,u1_pre_topc(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_pre_topc(sK1,X0)
        | ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(X0))
        | ~ l1_pre_topc(X0) ) )).

tff(u434,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( sK4(X0,sK3) != k9_subset_1(u1_struct_0(sK2),X1,k2_struct_0(sK3))
          | ~ r2_hidden(sK4(X0,sK3),u1_pre_topc(sK2))
          | ~ r2_hidden(X1,u1_pre_topc(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | m1_pre_topc(sK3,X0)
          | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(X0))
          | ~ l1_pre_topc(X0) )
    | ! [X1,X0] :
        ( sK4(X0,sK3) != k9_subset_1(u1_struct_0(sK2),X1,k2_struct_0(sK3))
        | ~ r2_hidden(sK4(X0,sK3),u1_pre_topc(sK2))
        | ~ r2_hidden(X1,u1_pre_topc(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_pre_topc(sK3,X0)
        | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(X0))
        | ~ l1_pre_topc(X0) ) )).

tff(u433,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

tff(u432,negated_conjecture,
    ( u1_struct_0(sK2) != u1_struct_0(sK3)
    | u1_struct_0(sK2) = u1_struct_0(sK3) )).

tff(u431,negated_conjecture,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | u1_pre_topc(sK0) = u1_pre_topc(sK1) )).

tff(u430,negated_conjecture,
    ( u1_pre_topc(sK2) != u1_pre_topc(sK3)
    | u1_pre_topc(sK2) = u1_pre_topc(sK3) )).

tff(u429,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = X2
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) )).

tff(u428,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) )).

tff(u427,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK0) )).

tff(u426,negated_conjecture,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK1) )).

tff(u425,negated_conjecture,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK2) )).

tff(u424,negated_conjecture,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK3) )).

tff(u423,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(X3,u1_pre_topc(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | sK6(X0,X2,X3) = k9_subset_1(u1_struct_0(X0),sK6(X1,X0,sK6(X0,X2,X3)),k2_struct_0(X0))
      | ~ l1_pre_topc(X2) ) )).

tff(u422,negated_conjecture,
    ( ~ ! [X5,X6] :
          ( ~ m1_pre_topc(X5,sK1)
          | ~ r2_hidden(X6,u1_pre_topc(X5))
          | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
          | r2_hidden(sK6(sK1,X5,X6),u1_pre_topc(sK0))
          | ~ l1_pre_topc(X5) )
    | ! [X5,X6] :
        ( ~ m1_pre_topc(X5,sK1)
        | ~ r2_hidden(X6,u1_pre_topc(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | r2_hidden(sK6(sK1,X5,X6),u1_pre_topc(sK0))
        | ~ l1_pre_topc(X5) ) )).

tff(u421,negated_conjecture,
    ( ~ ! [X5,X6] :
          ( ~ m1_pre_topc(X5,sK3)
          | ~ r2_hidden(X6,u1_pre_topc(X5))
          | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
          | r2_hidden(sK6(sK3,X5,X6),u1_pre_topc(sK2))
          | ~ l1_pre_topc(X5) )
    | ! [X5,X6] :
        ( ~ m1_pre_topc(X5,sK3)
        | ~ r2_hidden(X6,u1_pre_topc(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | r2_hidden(sK6(sK3,X5,X6),u1_pre_topc(sK2))
        | ~ l1_pre_topc(X5) ) )).

tff(u420,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_pre_topc(sK0,X1)
          | m1_pre_topc(sK1,X0)
          | ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(X0))
          | ~ l1_pre_topc(X0)
          | sK4(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK6(X1,sK0,sK4(X0,sK1)),k2_struct_0(sK0))
          | sK4(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK5(X0,sK1),k2_struct_0(sK1))
          | ~ l1_pre_topc(X1) )
    | ! [X1,X0] :
        ( ~ m1_pre_topc(sK0,X1)
        | m1_pre_topc(sK1,X0)
        | ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | sK4(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK6(X1,sK0,sK4(X0,sK1)),k2_struct_0(sK0))
        | sK4(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK5(X0,sK1),k2_struct_0(sK1))
        | ~ l1_pre_topc(X1) ) )).

tff(u419,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_pre_topc(sK0,X0)
          | ~ l1_pre_topc(X0)
          | ~ r2_hidden(X1,u1_pre_topc(sK2))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          | sK6(sK0,sK2,X1) = k9_subset_1(u1_struct_0(sK0),sK6(X0,sK0,sK6(sK0,sK2,X1)),k2_struct_0(sK0)) )
    | ! [X1,X0] :
        ( ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ r2_hidden(X1,u1_pre_topc(sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | sK6(sK0,sK2,X1) = k9_subset_1(u1_struct_0(sK0),sK6(X0,sK0,sK6(sK0,sK2,X1)),k2_struct_0(sK0)) ) )).

tff(u418,negated_conjecture,
    ( ~ ! [X3,X4] :
          ( ~ m1_pre_topc(sK1,X4)
          | k9_subset_1(u1_struct_0(sK0),sK6(X4,sK1,X3),k2_struct_0(sK1)) = X3
          | ~ r2_hidden(X3,u1_pre_topc(sK0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ l1_pre_topc(X4) )
    | ! [X3,X4] :
        ( ~ m1_pre_topc(sK1,X4)
        | k9_subset_1(u1_struct_0(sK0),sK6(X4,sK1,X3),k2_struct_0(sK1)) = X3
        | ~ r2_hidden(X3,u1_pre_topc(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(X4) ) )).

tff(u417,negated_conjecture,
    ( ~ ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK1) )).

tff(u416,negated_conjecture,
    ( ~ ! [X3,X4] :
          ( ~ m1_pre_topc(sK3,X4)
          | k9_subset_1(u1_struct_0(sK2),sK6(X4,sK3,X3),k2_struct_0(sK3)) = X3
          | ~ r2_hidden(X3,u1_pre_topc(sK2))
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
          | ~ l1_pre_topc(X4) )
    | ! [X3,X4] :
        ( ~ m1_pre_topc(sK3,X4)
        | k9_subset_1(u1_struct_0(sK2),sK6(X4,sK3,X3),k2_struct_0(sK3)) = X3
        | ~ r2_hidden(X3,u1_pre_topc(sK2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(X4) ) )).

tff(u415,negated_conjecture,
    ( ~ m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK2,sK0) )).

tff(u414,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | m1_pre_topc(X1,X0)
      | sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK6(X2,X1,sK4(X0,X1)),k2_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X2) ) )).

tff(u413,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X2))
      | ~ r2_hidden(X1,u1_pre_topc(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | m1_pre_topc(X0,X2)
      | k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) != sK4(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X2)
      | sK4(X2,X0) = k9_subset_1(u1_struct_0(X0),sK5(X2,X0),k2_struct_0(X0)) ) )).

tff(u412,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u411,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u410,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(X0))
          | m1_pre_topc(sK3,X0)
          | sK4(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK5(X0,sK3),k2_struct_0(sK3))
          | ~ l1_pre_topc(X0)
          | sK4(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK6(X1,sK2,sK4(X0,sK3)),k2_struct_0(sK2))
          | ~ m1_pre_topc(sK2,X1)
          | ~ l1_pre_topc(X1) )
    | ! [X1,X0] :
        ( ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(X0))
        | m1_pre_topc(sK3,X0)
        | sK4(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK5(X0,sK3),k2_struct_0(sK3))
        | ~ l1_pre_topc(X0)
        | sK4(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK6(X1,sK2,sK4(X0,sK3)),k2_struct_0(sK2))
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X1) ) )).

tff(u409,axiom,(
    ! [X1,X0] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u408,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) )).

tff(u407,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) )).

tff(u406,axiom,(
    ! [X1,X0,X6] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u405,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,k2_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
          | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,k2_struct_0(sK1)),u1_pre_topc(sK0))
          | ~ r2_hidden(X0,u1_pre_topc(X1))
          | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ m1_pre_topc(sK1,X1)
          | ~ l1_pre_topc(X1) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,k2_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,k2_struct_0(sK1)),u1_pre_topc(sK0))
        | ~ r2_hidden(X0,u1_pre_topc(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(sK1,X1)
        | ~ l1_pre_topc(X1) ) )).

tff(u404,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
          | r2_hidden(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK3)),u1_pre_topc(sK2))
          | ~ r2_hidden(X0,u1_pre_topc(X1))
          | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ m1_pre_topc(sK3,X1)
          | ~ l1_pre_topc(X1) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_hidden(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK3)),u1_pre_topc(sK2))
        | ~ r2_hidden(X0,u1_pre_topc(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1) ) )).

tff(u403,axiom,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) )).

tff(u402,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

tff(u401,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )).

tff(u400,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | m1_pre_topc(X1,X0)
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u399,negated_conjecture,
    ( ~ ! [X2] :
          ( m1_subset_1(sK4(X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
          | m1_pre_topc(sK1,X2)
          | ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(X2))
          | ~ l1_pre_topc(X2) )
    | ! [X2] :
        ( m1_subset_1(sK4(X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_pre_topc(sK1,X2)
        | ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(X2))
        | ~ l1_pre_topc(X2) ) )).

tff(u398,negated_conjecture,
    ( ~ ! [X4] :
          ( m1_subset_1(sK4(X4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
          | m1_pre_topc(sK3,X4)
          | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(X4))
          | ~ l1_pre_topc(X4) )
    | ! [X4] :
        ( m1_subset_1(sK4(X4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
        | m1_pre_topc(sK3,X4)
        | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(X4))
        | ~ l1_pre_topc(X4) ) )).

tff(u397,axiom,(
    ! [X1,X5,X0] :
      ( m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u396,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( m1_subset_1(sK6(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ r2_hidden(X1,u1_pre_topc(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X0,sK1)
          | ~ l1_pre_topc(X0) )
    | ! [X1,X0] :
        ( m1_subset_1(sK6(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,u1_pre_topc(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) ) )).

tff(u395,negated_conjecture,
    ( ~ ! [X3,X2] :
          ( m1_subset_1(sK6(sK3,X2,X3),k1_zfmisc_1(u1_struct_0(sK2)))
          | ~ r2_hidden(X3,u1_pre_topc(X2))
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          | ~ m1_pre_topc(X2,sK3)
          | ~ l1_pre_topc(X2) )
    | ! [X3,X2] :
        ( m1_subset_1(sK6(sK3,X2,X3),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X3,u1_pre_topc(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_pre_topc(X2,sK3)
        | ~ l1_pre_topc(X2) ) )).

tff(u394,axiom,(
    ! [X1,X5,X0] :
      ( ~ r2_hidden(X5,u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u393,axiom,(
    ! [X1,X3,X0] :
      ( ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(X1,X0)
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u392,axiom,(
    ! [X1,X5,X0] :
      ( r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u391,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK4(X0,X1),u1_pre_topc(X1))
      | sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
      | m1_pre_topc(X1,X0)
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u390,negated_conjecture,
    ( ~ ! [X2] :
          ( r2_hidden(sK4(X2,sK1),u1_pre_topc(sK0))
          | sK4(X2,sK1) = k9_subset_1(u1_struct_0(sK0),sK5(X2,sK1),k2_struct_0(sK1))
          | m1_pre_topc(sK1,X2)
          | ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(X2))
          | ~ l1_pre_topc(X2) )
    | ! [X2] :
        ( r2_hidden(sK4(X2,sK1),u1_pre_topc(sK0))
        | sK4(X2,sK1) = k9_subset_1(u1_struct_0(sK0),sK5(X2,sK1),k2_struct_0(sK1))
        | m1_pre_topc(sK1,X2)
        | ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(X2))
        | ~ l1_pre_topc(X2) ) )).

tff(u389,negated_conjecture,
    ( ~ ! [X2] :
          ( r2_hidden(sK4(X2,sK3),u1_pre_topc(sK2))
          | sK4(X2,sK3) = k9_subset_1(u1_struct_0(sK2),sK5(X2,sK3),k2_struct_0(sK3))
          | m1_pre_topc(sK3,X2)
          | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(X2))
          | ~ l1_pre_topc(X2) )
    | ! [X2] :
        ( r2_hidden(sK4(X2,sK3),u1_pre_topc(sK2))
        | sK4(X2,sK3) = k9_subset_1(u1_struct_0(sK2),sK5(X2,sK3),k2_struct_0(sK3))
        | m1_pre_topc(sK3,X2)
        | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(X2))
        | ~ l1_pre_topc(X2) ) )).

tff(u388,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:03:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (25402)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (25400)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (25419)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (25400)Refutation not found, incomplete strategy% (25400)------------------------------
% 0.20/0.50  % (25400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25400)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25400)Memory used [KB]: 10618
% 0.20/0.50  % (25400)Time elapsed: 0.092 s
% 0.20/0.50  % (25400)------------------------------
% 0.20/0.50  % (25400)------------------------------
% 0.20/0.50  % (25414)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (25418)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (25403)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (25413)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (25404)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (25420)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (25406)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (25406)Refutation not found, incomplete strategy% (25406)------------------------------
% 0.20/0.51  % (25406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25406)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (25406)Memory used [KB]: 10618
% 0.20/0.51  % (25406)Time elapsed: 0.106 s
% 0.20/0.51  % (25406)------------------------------
% 0.20/0.51  % (25406)------------------------------
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (25401)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (25405)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (25421)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (25423)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (25410)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (25401)Refutation not found, incomplete strategy% (25401)------------------------------
% 0.20/0.52  % (25401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25401)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25401)Memory used [KB]: 10746
% 0.20/0.52  % (25401)Time elapsed: 0.090 s
% 0.20/0.52  % (25401)------------------------------
% 0.20/0.52  % (25401)------------------------------
% 0.20/0.52  % (25411)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (25417)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (25422)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (25411)Refutation not found, incomplete strategy% (25411)------------------------------
% 0.20/0.52  % (25411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25411)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25411)Memory used [KB]: 10618
% 0.20/0.52  % (25411)Time elapsed: 0.109 s
% 0.20/0.52  % (25411)------------------------------
% 0.20/0.52  % (25411)------------------------------
% 0.20/0.52  % (25407)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (25407)Refutation not found, incomplete strategy% (25407)------------------------------
% 0.20/0.52  % (25407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25407)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25407)Memory used [KB]: 1663
% 0.20/0.52  % (25407)Time elapsed: 0.081 s
% 0.20/0.52  % (25407)------------------------------
% 0.20/0.52  % (25407)------------------------------
% 0.20/0.53  % (25409)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (25419)Refutation not found, incomplete strategy% (25419)------------------------------
% 0.20/0.53  % (25419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25412)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (25419)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25419)Memory used [KB]: 1791
% 0.20/0.53  % (25419)Time elapsed: 0.109 s
% 0.20/0.53  % (25419)------------------------------
% 0.20/0.53  % (25419)------------------------------
% 0.20/0.53  % (25416)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (25415)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (25402)# SZS output start Saturation.
% 0.20/0.53  tff(u439,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : (((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X1,X0)) | (u1_pre_topc(sK0) = X0))))) | (![X1, X0] : (((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X1,X0)) | (u1_pre_topc(sK0) = X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u438,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : (((g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (u1_struct_0(sK0) = X0))))) | (![X1, X0] : (((g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (u1_struct_0(sK0) = X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u437,negated_conjecture,
% 0.20/0.53      ((~(![X5, X4] : (((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X5,X4)) | (u1_pre_topc(sK2) = X4))))) | (![X5, X4] : (((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X5,X4)) | (u1_pre_topc(sK2) = X4)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u436,negated_conjecture,
% 0.20/0.53      ((~(![X5, X4] : (((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X4,X5)) | (u1_struct_0(sK2) = X4))))) | (![X5, X4] : (((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X4,X5)) | (u1_struct_0(sK2) = X4)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u435,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : (((sK4(X0,sK1) != k9_subset_1(u1_struct_0(sK0),X1,k2_struct_0(sK1))) | ~r2_hidden(sK4(X0,sK1),u1_pre_topc(sK0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK1,X0) | ~r1_tarski(k2_struct_0(sK1),k2_struct_0(X0)) | ~l1_pre_topc(X0))))) | (![X1, X0] : (((sK4(X0,sK1) != k9_subset_1(u1_struct_0(sK0),X1,k2_struct_0(sK1))) | ~r2_hidden(sK4(X0,sK1),u1_pre_topc(sK0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK1,X0) | ~r1_tarski(k2_struct_0(sK1),k2_struct_0(X0)) | ~l1_pre_topc(X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u434,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : (((sK4(X0,sK3) != k9_subset_1(u1_struct_0(sK2),X1,k2_struct_0(sK3))) | ~r2_hidden(sK4(X0,sK3),u1_pre_topc(sK2)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK3,X0) | ~r1_tarski(k2_struct_0(sK3),k2_struct_0(X0)) | ~l1_pre_topc(X0))))) | (![X1, X0] : (((sK4(X0,sK3) != k9_subset_1(u1_struct_0(sK2),X1,k2_struct_0(sK3))) | ~r2_hidden(sK4(X0,sK3),u1_pre_topc(sK2)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK3,X0) | ~r1_tarski(k2_struct_0(sK3),k2_struct_0(X0)) | ~l1_pre_topc(X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u433,negated_conjecture,
% 0.20/0.53      ((~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (u1_struct_0(sK0) = u1_struct_0(sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u432,negated_conjecture,
% 0.20/0.53      ((~(u1_struct_0(sK2) = u1_struct_0(sK3))) | (u1_struct_0(sK2) = u1_struct_0(sK3)))).
% 0.20/0.53  
% 0.20/0.53  tff(u431,negated_conjecture,
% 0.20/0.53      ((~(u1_pre_topc(sK0) = u1_pre_topc(sK1))) | (u1_pre_topc(sK0) = u1_pre_topc(sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u430,negated_conjecture,
% 0.20/0.53      ((~(u1_pre_topc(sK2) = u1_pre_topc(sK3))) | (u1_pre_topc(sK2) = u1_pre_topc(sK3)))).
% 0.20/0.53  
% 0.20/0.53  tff(u429,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~l1_pre_topc(X0) | (u1_pre_topc(X0) = X2) | (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u428,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~l1_pre_topc(X0) | (u1_struct_0(X0) = X1) | (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u427,negated_conjecture,
% 0.20/0.53      ((~l1_pre_topc(sK0)) | l1_pre_topc(sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u426,negated_conjecture,
% 0.20/0.53      ((~l1_pre_topc(sK1)) | l1_pre_topc(sK1))).
% 0.20/0.53  
% 0.20/0.53  tff(u425,negated_conjecture,
% 0.20/0.53      ((~l1_pre_topc(sK2)) | l1_pre_topc(sK2))).
% 0.20/0.53  
% 0.20/0.53  tff(u424,negated_conjecture,
% 0.20/0.53      ((~l1_pre_topc(sK3)) | l1_pre_topc(sK3))).
% 0.20/0.53  
% 0.20/0.53  tff(u423,axiom,
% 0.20/0.53      (![X1, X3, X0, X2] : ((~m1_pre_topc(X2,X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~r2_hidden(X3,u1_pre_topc(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | (sK6(X0,X2,X3) = k9_subset_1(u1_struct_0(X0),sK6(X1,X0,sK6(X0,X2,X3)),k2_struct_0(X0))) | ~l1_pre_topc(X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u422,negated_conjecture,
% 0.20/0.53      ((~(![X5, X6] : ((~m1_pre_topc(X5,sK1) | ~r2_hidden(X6,u1_pre_topc(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | r2_hidden(sK6(sK1,X5,X6),u1_pre_topc(sK0)) | ~l1_pre_topc(X5))))) | (![X5, X6] : ((~m1_pre_topc(X5,sK1) | ~r2_hidden(X6,u1_pre_topc(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | r2_hidden(sK6(sK1,X5,X6),u1_pre_topc(sK0)) | ~l1_pre_topc(X5)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u421,negated_conjecture,
% 0.20/0.53      ((~(![X5, X6] : ((~m1_pre_topc(X5,sK3) | ~r2_hidden(X6,u1_pre_topc(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | r2_hidden(sK6(sK3,X5,X6),u1_pre_topc(sK2)) | ~l1_pre_topc(X5))))) | (![X5, X6] : ((~m1_pre_topc(X5,sK3) | ~r2_hidden(X6,u1_pre_topc(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | r2_hidden(sK6(sK3,X5,X6),u1_pre_topc(sK2)) | ~l1_pre_topc(X5)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u420,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : ((~m1_pre_topc(sK0,X1) | m1_pre_topc(sK1,X0) | ~r1_tarski(k2_struct_0(sK1),k2_struct_0(X0)) | ~l1_pre_topc(X0) | (sK4(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK6(X1,sK0,sK4(X0,sK1)),k2_struct_0(sK0))) | (sK4(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK5(X0,sK1),k2_struct_0(sK1))) | ~l1_pre_topc(X1))))) | (![X1, X0] : ((~m1_pre_topc(sK0,X1) | m1_pre_topc(sK1,X0) | ~r1_tarski(k2_struct_0(sK1),k2_struct_0(X0)) | ~l1_pre_topc(X0) | (sK4(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK6(X1,sK0,sK4(X0,sK1)),k2_struct_0(sK0))) | (sK4(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK5(X0,sK1),k2_struct_0(sK1))) | ~l1_pre_topc(X1)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u419,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : ((~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | (sK6(sK0,sK2,X1) = k9_subset_1(u1_struct_0(sK0),sK6(X0,sK0,sK6(sK0,sK2,X1)),k2_struct_0(sK0))))))) | (![X1, X0] : ((~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | (sK6(sK0,sK2,X1) = k9_subset_1(u1_struct_0(sK0),sK6(X0,sK0,sK6(sK0,sK2,X1)),k2_struct_0(sK0)))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u418,negated_conjecture,
% 0.20/0.53      ((~(![X3, X4] : ((~m1_pre_topc(sK1,X4) | (k9_subset_1(u1_struct_0(sK0),sK6(X4,sK1,X3),k2_struct_0(sK1)) = X3) | ~r2_hidden(X3,u1_pre_topc(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(X4))))) | (![X3, X4] : ((~m1_pre_topc(sK1,X4) | (k9_subset_1(u1_struct_0(sK0),sK6(X4,sK1,X3),k2_struct_0(sK1)) = X3) | ~r2_hidden(X3,u1_pre_topc(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(X4)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u417,negated_conjecture,
% 0.20/0.53      ((~~m1_pre_topc(sK3,sK1)) | ~m1_pre_topc(sK3,sK1))).
% 0.20/0.53  
% 0.20/0.53  tff(u416,negated_conjecture,
% 0.20/0.53      ((~(![X3, X4] : ((~m1_pre_topc(sK3,X4) | (k9_subset_1(u1_struct_0(sK2),sK6(X4,sK3,X3),k2_struct_0(sK3)) = X3) | ~r2_hidden(X3,u1_pre_topc(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(X4))))) | (![X3, X4] : ((~m1_pre_topc(sK3,X4) | (k9_subset_1(u1_struct_0(sK2),sK6(X4,sK3,X3),k2_struct_0(sK3)) = X3) | ~r2_hidden(X3,u1_pre_topc(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(X4)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u415,negated_conjecture,
% 0.20/0.53      ((~m1_pre_topc(sK2,sK0)) | m1_pre_topc(sK2,sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u414,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | m1_pre_topc(X1,X0) | (sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | (sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK6(X2,X1,sK4(X0,X1)),k2_struct_0(X1))) | ~m1_pre_topc(X1,X2) | ~l1_pre_topc(X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u413,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~r1_tarski(k2_struct_0(X0),k2_struct_0(X2)) | ~r2_hidden(X1,u1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | m1_pre_topc(X0,X2) | (k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) != sK4(X2,X0)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X2) | (sK4(X2,X0) = k9_subset_1(u1_struct_0(X0),sK5(X2,X0),k2_struct_0(X0))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u412,axiom,
% 0.20/0.53      (![X1, X0] : ((~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u411,axiom,
% 0.20/0.53      (![X1, X0] : ((~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u410,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : ((~r1_tarski(k2_struct_0(sK3),k2_struct_0(X0)) | m1_pre_topc(sK3,X0) | (sK4(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK5(X0,sK3),k2_struct_0(sK3))) | ~l1_pre_topc(X0) | (sK4(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK6(X1,sK2,sK4(X0,sK3)),k2_struct_0(sK2))) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1))))) | (![X1, X0] : ((~r1_tarski(k2_struct_0(sK3),k2_struct_0(X0)) | m1_pre_topc(sK3,X0) | (sK4(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK5(X0,sK3),k2_struct_0(sK3))) | ~l1_pre_topc(X0) | (sK4(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK6(X1,sK2,sK4(X0,sK3)),k2_struct_0(sK2))) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u409,axiom,
% 0.20/0.53      (![X1, X0] : ((r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u408,axiom,
% 0.20/0.53      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | (X1 = X3))))).
% 0.20/0.53  
% 0.20/0.53  tff(u407,axiom,
% 0.20/0.53      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | (X0 = X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u406,axiom,
% 0.20/0.53      (![X1, X0, X6] : ((~m1_subset_1(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u405,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : ((~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,k2_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,k2_struct_0(sK1)),u1_pre_topc(sK0)) | ~r2_hidden(X0,u1_pre_topc(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1))))) | (![X1, X0] : ((~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,k2_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k9_subset_1(u1_struct_0(sK0),X0,k2_struct_0(sK1)),u1_pre_topc(sK0)) | ~r2_hidden(X0,u1_pre_topc(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u404,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : ((~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | r2_hidden(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK3)),u1_pre_topc(sK2)) | ~r2_hidden(X0,u1_pre_topc(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1))))) | (![X1, X0] : ((~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | r2_hidden(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK3)),u1_pre_topc(sK2)) | ~r2_hidden(X0,u1_pre_topc(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u403,axiom,
% 0.20/0.53      (![X0] : ((m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u402,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u401,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u400,axiom,
% 0.20/0.53      (![X1, X0] : ((m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | m1_pre_topc(X1,X0) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u399,negated_conjecture,
% 0.20/0.53      ((~(![X2] : ((m1_subset_1(sK4(X2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(sK1,X2) | ~r1_tarski(k2_struct_0(sK1),k2_struct_0(X2)) | ~l1_pre_topc(X2))))) | (![X2] : ((m1_subset_1(sK4(X2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(sK1,X2) | ~r1_tarski(k2_struct_0(sK1),k2_struct_0(X2)) | ~l1_pre_topc(X2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u398,negated_conjecture,
% 0.20/0.53      ((~(![X4] : ((m1_subset_1(sK4(X4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | m1_pre_topc(sK3,X4) | ~r1_tarski(k2_struct_0(sK3),k2_struct_0(X4)) | ~l1_pre_topc(X4))))) | (![X4] : ((m1_subset_1(sK4(X4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | m1_pre_topc(sK3,X4) | ~r1_tarski(k2_struct_0(sK3),k2_struct_0(X4)) | ~l1_pre_topc(X4)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u397,axiom,
% 0.20/0.53      (![X1, X5, X0] : ((m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X5,u1_pre_topc(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u396,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : ((m1_subset_1(sK6(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(X0))))) | (![X1, X0] : ((m1_subset_1(sK6(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u395,negated_conjecture,
% 0.20/0.53      ((~(![X3, X2] : ((m1_subset_1(sK6(sK3,X2,X3),k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X3,u1_pre_topc(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X2,sK3) | ~l1_pre_topc(X2))))) | (![X3, X2] : ((m1_subset_1(sK6(sK3,X2,X3),k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X3,u1_pre_topc(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X2,sK3) | ~l1_pre_topc(X2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u394,axiom,
% 0.20/0.53      (![X1, X5, X0] : ((~r2_hidden(X5,u1_pre_topc(X1)) | (k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u393,axiom,
% 0.20/0.53      (![X1, X3, X0] : ((~r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) | (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(X1,X0) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u392,axiom,
% 0.20/0.53      (![X1, X5, X0] : ((r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u391,axiom,
% 0.20/0.53      (![X1, X0] : ((r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) | (sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))) | m1_pre_topc(X1,X0) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u390,negated_conjecture,
% 0.20/0.53      ((~(![X2] : ((r2_hidden(sK4(X2,sK1),u1_pre_topc(sK0)) | (sK4(X2,sK1) = k9_subset_1(u1_struct_0(sK0),sK5(X2,sK1),k2_struct_0(sK1))) | m1_pre_topc(sK1,X2) | ~r1_tarski(k2_struct_0(sK1),k2_struct_0(X2)) | ~l1_pre_topc(X2))))) | (![X2] : ((r2_hidden(sK4(X2,sK1),u1_pre_topc(sK0)) | (sK4(X2,sK1) = k9_subset_1(u1_struct_0(sK0),sK5(X2,sK1),k2_struct_0(sK1))) | m1_pre_topc(sK1,X2) | ~r1_tarski(k2_struct_0(sK1),k2_struct_0(X2)) | ~l1_pre_topc(X2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u389,negated_conjecture,
% 0.20/0.53      ((~(![X2] : ((r2_hidden(sK4(X2,sK3),u1_pre_topc(sK2)) | (sK4(X2,sK3) = k9_subset_1(u1_struct_0(sK2),sK5(X2,sK3),k2_struct_0(sK3))) | m1_pre_topc(sK3,X2) | ~r1_tarski(k2_struct_0(sK3),k2_struct_0(X2)) | ~l1_pre_topc(X2))))) | (![X2] : ((r2_hidden(sK4(X2,sK3),u1_pre_topc(sK2)) | (sK4(X2,sK3) = k9_subset_1(u1_struct_0(sK2),sK5(X2,sK3),k2_struct_0(sK3))) | m1_pre_topc(sK3,X2) | ~r1_tarski(k2_struct_0(sK3),k2_struct_0(X2)) | ~l1_pre_topc(X2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u388,axiom,
% 0.20/0.53      (![X0] : ((l1_struct_0(X0) | ~l1_pre_topc(X0))))).
% 0.20/0.53  
% 0.20/0.53  % (25402)# SZS output end Saturation.
% 0.20/0.53  % (25402)------------------------------
% 0.20/0.53  % (25402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25402)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (25402)Memory used [KB]: 6396
% 0.20/0.53  % (25402)Time elapsed: 0.101 s
% 0.20/0.53  % (25402)------------------------------
% 0.20/0.53  % (25402)------------------------------
% 0.20/0.53  % (25399)Success in time 0.168 s
%------------------------------------------------------------------------------
