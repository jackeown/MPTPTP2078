%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0391+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C7berACXdX

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   49 (  56 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  225 ( 282 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_23_type,type,(
    sk_C_23: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_10_type,type,(
    sk_B_10: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t9_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( A @ B ) )
        & ( r1_xboole_0 @ ( A @ C ) ) )
     => ( r1_xboole_0 @ ( k1_setfam_1 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ ( A @ B ) )
          & ( r1_xboole_0 @ ( A @ C ) ) )
       => ( r1_xboole_0 @ ( k1_setfam_1 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_setfam_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_setfam_1 @ sk_B_10 @ sk_C_23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_A_2 @ sk_B_10 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X1827: $i,X1828: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X1827 @ X1828 ) )
      | ~ ( r2_hidden @ ( X1828 @ X1827 ) ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B_10 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_C_23 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_C_23 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X104: $i,X105: $i] :
      ( ( k4_xboole_0 @ ( X104 @ X105 ) )
      = ( k5_xboole_0 @ ( X104 @ ( k3_xboole_0 @ ( X104 @ X105 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('10',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X104: $i,X105: $i] :
      ( ( k6_subset_1 @ ( X104 @ X105 ) )
      = ( k5_xboole_0 @ ( X104 @ ( k3_xboole_0 @ ( X104 @ X105 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k6_subset_1 @ ( sk_A_2 @ sk_C_23 ) )
    = ( k5_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( B @ A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('14',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ k1_xboole_0 ) )
      = X302 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ o_0_0_xboole_0 ) )
      = X302 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k6_subset_1 @ ( sk_A_2 @ sk_C_23 ) )
    = sk_A_2 ),
    inference(demod,[status(thm)],['12','13','18'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
     => ( ( r1_tarski @ ( A @ B ) )
        & ( r1_xboole_0 @ ( A @ C ) ) ) ) )).

thf('20',plain,(
    ! [X118: $i,X119: $i,X120: $i] :
      ( ( r1_xboole_0 @ ( X118 @ X120 ) )
      | ~ ( r1_tarski @ ( X118 @ ( k4_xboole_0 @ ( X119 @ X120 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('21',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X118: $i,X119: $i,X120: $i] :
      ( ( r1_xboole_0 @ ( X118 @ X120 ) )
      | ~ ( r1_tarski @ ( X118 @ ( k6_subset_1 @ ( X119 @ X120 ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ sk_A_2 ) )
      | ( r1_xboole_0 @ ( X0 @ sk_C_23 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    r1_xboole_0 @ ( k1_setfam_1 @ sk_B_10 @ sk_C_23 ) ),
    inference('sup-',[status(thm)],['3','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
