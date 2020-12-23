%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.clX5jxmJmo

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:09 EST 2020

% Result     : Theorem 38.45s
% Output     : Refutation 38.45s
% Verified   : 
% Statistics : Number of formulae       :   80 (  94 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  619 ( 784 expanded)
%              Number of equality atoms :   56 (  68 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(t47_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t47_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X31 @ X32 ) @ X31 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k3_xboole_0 @ X23 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( o_0_0_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( o_0_0_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('39',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X33 @ X34 ) @ X35 )
      = ( k4_xboole_0 @ X33 @ ( k2_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ X22 @ X21 )
        = X21 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','50'])).

thf('52',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.clX5jxmJmo
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:28:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 38.45/38.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 38.45/38.66  % Solved by: fo/fo7.sh
% 38.45/38.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 38.45/38.66  % done 16160 iterations in 38.189s
% 38.45/38.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 38.45/38.66  % SZS output start Refutation
% 38.45/38.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 38.45/38.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 38.45/38.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 38.45/38.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 38.45/38.66  thf(sk_B_type, type, sk_B: $i).
% 38.45/38.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 38.45/38.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 38.45/38.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 38.45/38.66  thf(sk_A_type, type, sk_A: $i).
% 38.45/38.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 38.45/38.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 38.45/38.66  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 38.45/38.66  thf(t47_xboole_1, conjecture,
% 38.45/38.66    (![A:$i,B:$i]:
% 38.45/38.66     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 38.45/38.66  thf(zf_stmt_0, negated_conjecture,
% 38.45/38.66    (~( ![A:$i,B:$i]:
% 38.45/38.66        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 38.45/38.66          ( k4_xboole_0 @ A @ B ) ) )),
% 38.45/38.66    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 38.45/38.66  thf('0', plain,
% 38.45/38.66      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 38.45/38.66         != (k4_xboole_0 @ sk_A @ sk_B))),
% 38.45/38.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.45/38.66  thf(commutativity_k3_xboole_0, axiom,
% 38.45/38.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 38.45/38.66  thf('1', plain,
% 38.45/38.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 38.45/38.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 38.45/38.66  thf('2', plain,
% 38.45/38.66      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 38.45/38.66         != (k4_xboole_0 @ sk_A @ sk_B))),
% 38.45/38.66      inference('demod', [status(thm)], ['0', '1'])).
% 38.45/38.66  thf(t36_xboole_1, axiom,
% 38.45/38.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 38.45/38.66  thf('3', plain,
% 38.45/38.66      (![X31 : $i, X32 : $i]: (r1_tarski @ (k4_xboole_0 @ X31 @ X32) @ X31)),
% 38.45/38.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 38.45/38.66  thf(t28_xboole_1, axiom,
% 38.45/38.66    (![A:$i,B:$i]:
% 38.45/38.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 38.45/38.66  thf('4', plain,
% 38.45/38.66      (![X29 : $i, X30 : $i]:
% 38.45/38.66         (((k3_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_tarski @ X29 @ X30))),
% 38.45/38.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 38.45/38.66  thf('5', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 38.45/38.66           = (k4_xboole_0 @ X0 @ X1))),
% 38.45/38.66      inference('sup-', [status(thm)], ['3', '4'])).
% 38.45/38.66  thf('6', plain,
% 38.45/38.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 38.45/38.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 38.45/38.66  thf('7', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 38.45/38.66           = (k4_xboole_0 @ X0 @ X1))),
% 38.45/38.66      inference('demod', [status(thm)], ['5', '6'])).
% 38.45/38.66  thf(t3_xboole_0, axiom,
% 38.45/38.66    (![A:$i,B:$i]:
% 38.45/38.66     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 38.45/38.66            ( r1_xboole_0 @ A @ B ) ) ) & 
% 38.45/38.66       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 38.45/38.66            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 38.45/38.66  thf('8', plain,
% 38.45/38.66      (![X14 : $i, X15 : $i]:
% 38.45/38.66         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C @ X15 @ X14) @ X15))),
% 38.45/38.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 38.45/38.66  thf('9', plain,
% 38.45/38.66      (![X14 : $i, X15 : $i]:
% 38.45/38.66         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C @ X15 @ X14) @ X14))),
% 38.45/38.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 38.45/38.66  thf(d5_xboole_0, axiom,
% 38.45/38.66    (![A:$i,B:$i,C:$i]:
% 38.45/38.66     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 38.45/38.66       ( ![D:$i]:
% 38.45/38.66         ( ( r2_hidden @ D @ C ) <=>
% 38.45/38.66           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 38.45/38.66  thf('10', plain,
% 38.45/38.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 38.45/38.66         (~ (r2_hidden @ X8 @ X7)
% 38.45/38.66          | ~ (r2_hidden @ X8 @ X6)
% 38.45/38.66          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 38.45/38.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.45/38.66  thf('11', plain,
% 38.45/38.66      (![X5 : $i, X6 : $i, X8 : $i]:
% 38.45/38.66         (~ (r2_hidden @ X8 @ X6)
% 38.45/38.66          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 38.45/38.66      inference('simplify', [status(thm)], ['10'])).
% 38.45/38.66  thf('12', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.45/38.66         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 38.45/38.66          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 38.45/38.66      inference('sup-', [status(thm)], ['9', '11'])).
% 38.45/38.66  thf('13', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 38.45/38.66          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 38.45/38.66      inference('sup-', [status(thm)], ['8', '12'])).
% 38.45/38.66  thf('14', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 38.45/38.66      inference('simplify', [status(thm)], ['13'])).
% 38.45/38.66  thf(d7_xboole_0, axiom,
% 38.45/38.66    (![A:$i,B:$i]:
% 38.45/38.66     ( ( r1_xboole_0 @ A @ B ) <=>
% 38.45/38.66       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 38.45/38.66  thf('15', plain,
% 38.45/38.66      (![X10 : $i, X11 : $i]:
% 38.45/38.66         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 38.45/38.66          | ~ (r1_xboole_0 @ X10 @ X11))),
% 38.45/38.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 38.45/38.66  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 38.45/38.66  thf('16', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 38.45/38.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 38.45/38.66  thf('17', plain,
% 38.45/38.66      (![X10 : $i, X11 : $i]:
% 38.45/38.66         (((k3_xboole_0 @ X10 @ X11) = (o_0_0_xboole_0))
% 38.45/38.66          | ~ (r1_xboole_0 @ X10 @ X11))),
% 38.45/38.66      inference('demod', [status(thm)], ['15', '16'])).
% 38.45/38.66  thf('18', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (o_0_0_xboole_0))),
% 38.45/38.66      inference('sup-', [status(thm)], ['14', '17'])).
% 38.45/38.66  thf('19', plain,
% 38.45/38.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 38.45/38.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 38.45/38.66  thf('20', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 38.45/38.66      inference('demod', [status(thm)], ['18', '19'])).
% 38.45/38.66  thf(t16_xboole_1, axiom,
% 38.45/38.66    (![A:$i,B:$i,C:$i]:
% 38.45/38.66     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 38.45/38.66       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 38.45/38.66  thf('21', plain,
% 38.45/38.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 38.45/38.66         ((k3_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25)
% 38.45/38.66           = (k3_xboole_0 @ X23 @ (k3_xboole_0 @ X24 @ X25)))),
% 38.45/38.66      inference('cnf', [status(esa)], [t16_xboole_1])).
% 38.45/38.66  thf('22', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.45/38.66         ((o_0_0_xboole_0)
% 38.45/38.66           = (k3_xboole_0 @ X1 @ 
% 38.45/38.66              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))))),
% 38.45/38.66      inference('sup+', [status(thm)], ['20', '21'])).
% 38.45/38.66  thf('23', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((o_0_0_xboole_0)
% 38.45/38.66           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 38.45/38.66      inference('sup+', [status(thm)], ['7', '22'])).
% 38.45/38.66  thf('24', plain,
% 38.45/38.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 38.45/38.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 38.45/38.66  thf('25', plain,
% 38.45/38.66      (![X10 : $i, X12 : $i]:
% 38.45/38.66         ((r1_xboole_0 @ X10 @ X12)
% 38.45/38.66          | ((k3_xboole_0 @ X10 @ X12) != (k1_xboole_0)))),
% 38.45/38.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 38.45/38.66  thf('26', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 38.45/38.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 38.45/38.66  thf('27', plain,
% 38.45/38.66      (![X10 : $i, X12 : $i]:
% 38.45/38.66         ((r1_xboole_0 @ X10 @ X12)
% 38.45/38.66          | ((k3_xboole_0 @ X10 @ X12) != (o_0_0_xboole_0)))),
% 38.45/38.66      inference('demod', [status(thm)], ['25', '26'])).
% 38.45/38.66  thf('28', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         (((k3_xboole_0 @ X1 @ X0) != (o_0_0_xboole_0))
% 38.45/38.66          | (r1_xboole_0 @ X0 @ X1))),
% 38.45/38.66      inference('sup-', [status(thm)], ['24', '27'])).
% 38.45/38.66  thf('29', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 38.45/38.66          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 38.45/38.66      inference('sup-', [status(thm)], ['23', '28'])).
% 38.45/38.66  thf('30', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X1)),
% 38.45/38.66      inference('simplify', [status(thm)], ['29'])).
% 38.45/38.66  thf('31', plain,
% 38.45/38.66      (![X5 : $i, X6 : $i, X9 : $i]:
% 38.45/38.66         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 38.45/38.66          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 38.45/38.66          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 38.45/38.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.45/38.66  thf('32', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 38.45/38.66          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.45/38.66      inference('eq_fact', [status(thm)], ['31'])).
% 38.45/38.66  thf('33', plain,
% 38.45/38.66      (![X5 : $i, X6 : $i, X9 : $i]:
% 38.45/38.66         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 38.45/38.66          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 38.45/38.66          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 38.45/38.66          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 38.45/38.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.45/38.66  thf('34', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 38.45/38.66          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 38.45/38.66          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 38.45/38.66          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.45/38.66      inference('sup-', [status(thm)], ['32', '33'])).
% 38.45/38.66  thf('35', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 38.45/38.66          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 38.45/38.66          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.45/38.66      inference('simplify', [status(thm)], ['34'])).
% 38.45/38.66  thf('36', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 38.45/38.66          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.45/38.66      inference('eq_fact', [status(thm)], ['31'])).
% 38.45/38.66  thf('37', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 38.45/38.66          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 38.45/38.66      inference('clc', [status(thm)], ['35', '36'])).
% 38.45/38.66  thf('38', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 38.45/38.66          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 38.45/38.66      inference('eq_fact', [status(thm)], ['31'])).
% 38.45/38.66  thf('39', plain,
% 38.45/38.66      (![X14 : $i, X16 : $i, X17 : $i]:
% 38.45/38.66         (~ (r2_hidden @ X16 @ X14)
% 38.45/38.66          | ~ (r2_hidden @ X16 @ X17)
% 38.45/38.66          | ~ (r1_xboole_0 @ X14 @ X17))),
% 38.45/38.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 38.45/38.66  thf('40', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.45/38.66         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 38.45/38.66          | ~ (r1_xboole_0 @ X0 @ X2)
% 38.45/38.66          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2))),
% 38.45/38.66      inference('sup-', [status(thm)], ['38', '39'])).
% 38.45/38.66  thf('41', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         (((X1) = (k4_xboole_0 @ X1 @ X0))
% 38.45/38.66          | ~ (r1_xboole_0 @ X1 @ X0)
% 38.45/38.66          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 38.45/38.66      inference('sup-', [status(thm)], ['37', '40'])).
% 38.45/38.66  thf('42', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         (~ (r1_xboole_0 @ X1 @ X0) | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 38.45/38.66      inference('simplify', [status(thm)], ['41'])).
% 38.45/38.66  thf('43', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 38.45/38.66           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 38.45/38.66      inference('sup-', [status(thm)], ['30', '42'])).
% 38.45/38.66  thf(t41_xboole_1, axiom,
% 38.45/38.66    (![A:$i,B:$i,C:$i]:
% 38.45/38.66     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 38.45/38.66       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 38.45/38.66  thf('44', plain,
% 38.45/38.66      (![X33 : $i, X34 : $i, X35 : $i]:
% 38.45/38.66         ((k4_xboole_0 @ (k4_xboole_0 @ X33 @ X34) @ X35)
% 38.45/38.66           = (k4_xboole_0 @ X33 @ (k2_xboole_0 @ X34 @ X35)))),
% 38.45/38.66      inference('cnf', [status(esa)], [t41_xboole_1])).
% 38.45/38.66  thf(commutativity_k2_xboole_0, axiom,
% 38.45/38.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 38.45/38.66  thf('45', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 38.45/38.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 38.45/38.66  thf(t17_xboole_1, axiom,
% 38.45/38.66    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 38.45/38.66  thf('46', plain,
% 38.45/38.66      (![X26 : $i, X27 : $i]: (r1_tarski @ (k3_xboole_0 @ X26 @ X27) @ X26)),
% 38.45/38.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 38.45/38.66  thf(t12_xboole_1, axiom,
% 38.45/38.66    (![A:$i,B:$i]:
% 38.45/38.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 38.45/38.66  thf('47', plain,
% 38.45/38.66      (![X21 : $i, X22 : $i]:
% 38.45/38.66         (((k2_xboole_0 @ X22 @ X21) = (X21)) | ~ (r1_tarski @ X22 @ X21))),
% 38.45/38.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 38.45/38.66  thf('48', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 38.45/38.66      inference('sup-', [status(thm)], ['46', '47'])).
% 38.45/38.66  thf('49', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 38.45/38.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 38.45/38.66  thf('50', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 38.45/38.66      inference('demod', [status(thm)], ['48', '49'])).
% 38.45/38.66  thf('51', plain,
% 38.45/38.66      (![X0 : $i, X1 : $i]:
% 38.45/38.66         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 38.45/38.66           = (k4_xboole_0 @ X1 @ X0))),
% 38.45/38.66      inference('demod', [status(thm)], ['43', '44', '45', '50'])).
% 38.45/38.66  thf('52', plain,
% 38.45/38.66      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 38.45/38.66      inference('demod', [status(thm)], ['2', '51'])).
% 38.45/38.66  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 38.45/38.66  
% 38.45/38.66  % SZS output end Refutation
% 38.45/38.66  
% 38.45/38.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
