%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1957+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.78fcJVvTS9

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:06 EST 2020

% Result     : Theorem 3.66s
% Output     : Refutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_A_97_type,type,(
    sk_A_97: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(t4_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
        = ( k9_setfam_1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t4_waybel_7])).

thf('0',plain,(
    ( u1_struct_0 @ ( k3_yellow_1 @ sk_A_97 ) )
 != ( k9_setfam_1 @ sk_A_97 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X10109: $i] :
      ( ( k3_yellow_1 @ X10109 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X10109 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X10087: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X10087 ) )
      = X10087 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k9_setfam_1 @ sk_A_97 )
 != ( k9_setfam_1 @ sk_A_97 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
