%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NA4pdQBqsi

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:18 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 807 expanded)
%              Number of leaves         :   14 ( 273 expanded)
%              Depth                    :   18
%              Number of atoms          : 1074 (8478 expanded)
%              Number of equality atoms :   88 ( 747 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t51_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t51_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['0','5'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','34'])).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['64','66'])).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','70'])).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X2 ) @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('75',plain,(
    ! [X0: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','70'])).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['73','78','79','87'])).

thf('89',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['6','88'])).

thf('90',plain,(
    $false ),
    inference(simplify,[status(thm)],['89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NA4pdQBqsi
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:13:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.93  % Solved by: fo/fo7.sh
% 0.76/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.93  % done 503 iterations in 0.477s
% 0.76/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.93  % SZS output start Refutation
% 0.76/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.93  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.76/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.93  thf(t51_xboole_1, conjecture,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.76/0.93       ( A ) ))).
% 0.76/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.93    (~( ![A:$i,B:$i]:
% 0.76/0.93        ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.76/0.93          ( A ) ) )),
% 0.76/0.93    inference('cnf.neg', [status(esa)], [t51_xboole_1])).
% 0.76/0.93  thf('0', plain,
% 0.76/0.93      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.76/0.93         (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.76/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.93  thf(t47_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.76/0.93  thf('1', plain,
% 0.76/0.93      (![X13 : $i, X14 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.76/0.93           = (k4_xboole_0 @ X13 @ X14))),
% 0.76/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.76/0.93  thf(t39_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.93  thf('2', plain,
% 0.76/0.93      (![X11 : $i, X12 : $i]:
% 0.76/0.93         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.76/0.93           = (k2_xboole_0 @ X11 @ X12))),
% 0.76/0.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.93  thf('3', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.76/0.93      inference('sup+', [status(thm)], ['1', '2'])).
% 0.76/0.93  thf(commutativity_k2_xboole_0, axiom,
% 0.76/0.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.76/0.93  thf('4', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.93  thf('5', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['3', '4'])).
% 0.76/0.93  thf('6', plain,
% 0.76/0.93      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.76/0.93      inference('demod', [status(thm)], ['0', '5'])).
% 0.76/0.93  thf(d5_xboole_0, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.76/0.93       ( ![D:$i]:
% 0.76/0.93         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.93           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.76/0.93  thf('7', plain,
% 0.76/0.93      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.76/0.93         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.76/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.76/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.76/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.93  thf('8', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/0.93          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.93      inference('eq_fact', [status(thm)], ['7'])).
% 0.76/0.93  thf('9', plain,
% 0.76/0.93      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.76/0.93         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.76/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.76/0.93          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.76/0.93          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.76/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.93  thf('10', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.76/0.93          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/0.93          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.76/0.93          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.93  thf('11', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.76/0.93          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/0.93          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.93      inference('simplify', [status(thm)], ['10'])).
% 0.76/0.93  thf('12', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/0.93          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.93      inference('eq_fact', [status(thm)], ['7'])).
% 0.76/0.93  thf('13', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.76/0.93          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.76/0.93      inference('clc', [status(thm)], ['11', '12'])).
% 0.76/0.93  thf('14', plain,
% 0.76/0.93      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.76/0.93         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.76/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.76/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.76/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.93  thf('15', plain,
% 0.76/0.93      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.76/0.93         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.76/0.93          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.76/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.76/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.93  thf('16', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.76/0.93          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.76/0.93          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.76/0.93          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.76/0.93      inference('sup-', [status(thm)], ['14', '15'])).
% 0.76/0.93  thf('17', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.76/0.93          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.76/0.93      inference('simplify', [status(thm)], ['16'])).
% 0.76/0.93  thf(t48_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.93  thf('18', plain,
% 0.76/0.93      (![X15 : $i, X16 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.93           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.93  thf('19', plain,
% 0.76/0.93      (![X15 : $i, X16 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.93           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.93  thf('20', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['18', '19'])).
% 0.76/0.93  thf('21', plain,
% 0.76/0.93      (![X13 : $i, X14 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.76/0.93           = (k4_xboole_0 @ X13 @ X14))),
% 0.76/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.76/0.93  thf('22', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ X0)
% 0.76/0.93           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['20', '21'])).
% 0.76/0.93  thf('23', plain,
% 0.76/0.93      (![X13 : $i, X14 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.76/0.93           = (k4_xboole_0 @ X13 @ X14))),
% 0.76/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.76/0.93  thf('24', plain,
% 0.76/0.93      (![X15 : $i, X16 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.93           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.93  thf(l36_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.76/0.93       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.76/0.93  thf('25', plain,
% 0.76/0.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X8 @ X10)))),
% 0.76/0.93      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.76/0.93  thf('26', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['24', '25'])).
% 0.76/0.93  thf('27', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['23', '26'])).
% 0.76/0.93  thf('28', plain,
% 0.76/0.93      (![X15 : $i, X16 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.93           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.93  thf('29', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X1 @ X0)
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['27', '28'])).
% 0.76/0.93  thf('30', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['22', '29'])).
% 0.76/0.93  thf('31', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ X0)
% 0.76/0.93           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['20', '21'])).
% 0.76/0.93  thf('32', plain,
% 0.76/0.93      (![X13 : $i, X14 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.76/0.93           = (k4_xboole_0 @ X13 @ X14))),
% 0.76/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.76/0.93  thf('33', plain,
% 0.76/0.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X8 @ X10)))),
% 0.76/0.93      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.76/0.93  thf('34', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['32', '33'])).
% 0.76/0.93  thf('35', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ X0)
% 0.76/0.93           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X1) @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['30', '31', '34'])).
% 0.76/0.93  thf('36', plain,
% 0.76/0.93      (![X15 : $i, X16 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.93           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.93  thf('37', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X1) @ X0)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['35', '36'])).
% 0.76/0.93  thf('38', plain,
% 0.76/0.93      (![X15 : $i, X16 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.93           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.93  thf('39', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X1 @ X0)
% 0.76/0.93           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X1) @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['37', '38'])).
% 0.76/0.93  thf('40', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ X0)
% 0.76/0.93           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['20', '21'])).
% 0.76/0.93  thf('41', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X1 @ X0)
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['27', '28'])).
% 0.76/0.93  thf('42', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.93  thf('43', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1))
% 0.76/0.93           = (k3_xboole_0 @ X1 @ X0))),
% 0.76/0.93      inference('sup+', [status(thm)], ['41', '42'])).
% 0.76/0.93  thf('44', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1))
% 0.76/0.93           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['40', '43'])).
% 0.76/0.93  thf('45', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['32', '33'])).
% 0.76/0.93  thf('46', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ X0)
% 0.76/0.93           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['20', '21'])).
% 0.76/0.93  thf('47', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 0.76/0.93           = (k4_xboole_0 @ X1 @ X0))),
% 0.76/0.93      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.76/0.93  thf('48', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X1 @ X0)
% 0.76/0.93           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['20', '21'])).
% 0.76/0.94  thf('49', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.76/0.94           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['24', '25'])).
% 0.76/0.94  thf('50', plain,
% 0.76/0.94      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X6 @ X5)
% 0.76/0.94          | ~ (r2_hidden @ X6 @ X4)
% 0.76/0.94          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.76/0.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.94  thf('51', plain,
% 0.76/0.94      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X6 @ X4)
% 0.76/0.94          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['50'])).
% 0.76/0.94  thf('52', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X3 @ 
% 0.76/0.94             (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.76/0.94          | ~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['49', '51'])).
% 0.76/0.94  thf('53', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X3 @ 
% 0.76/0.94             (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))
% 0.76/0.94          | ~ (r2_hidden @ X3 @ 
% 0.76/0.94               (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['48', '52'])).
% 0.76/0.94  thf('54', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 0.76/0.94           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['32', '33'])).
% 0.76/0.94  thf('55', plain,
% 0.76/0.94      (![X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.94           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('56', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X3 @ 
% 0.76/0.94             (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0)))
% 0.76/0.94          | ~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.76/0.94      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.76/0.94  thf('57', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.94          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X1))))),
% 0.76/0.94      inference('sup-', [status(thm)], ['47', '56'])).
% 0.76/0.94  thf('58', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))
% 0.76/0.94          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['39', '57'])).
% 0.76/0.94  thf('59', plain,
% 0.76/0.94      (![X13 : $i, X14 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.76/0.94           = (k4_xboole_0 @ X13 @ X14))),
% 0.76/0.94      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.76/0.94  thf('60', plain,
% 0.76/0.94      (![X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.94           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('61', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.94           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['59', '60'])).
% 0.76/0.94  thf('62', plain,
% 0.76/0.94      (![X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.94           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('63', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.94           = (k3_xboole_0 @ X1 @ X0))),
% 0.76/0.94      inference('sup+', [status(thm)], ['61', '62'])).
% 0.76/0.94  thf('64', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 0.76/0.94          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['58', '63'])).
% 0.76/0.94  thf('65', plain,
% 0.76/0.94      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.76/0.94         (~ (r2_hidden @ X6 @ X5)
% 0.76/0.94          | (r2_hidden @ X6 @ X3)
% 0.76/0.94          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.76/0.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.94  thf('66', plain,
% 0.76/0.94      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.76/0.94         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.76/0.94      inference('simplify', [status(thm)], ['65'])).
% 0.76/0.94  thf('67', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0))),
% 0.76/0.94      inference('clc', [status(thm)], ['64', '66'])).
% 0.76/0.94  thf('68', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0)
% 0.76/0.94           = (k4_xboole_0 @ X1 @ X1))),
% 0.76/0.94      inference('sup-', [status(thm)], ['17', '67'])).
% 0.76/0.94  thf('69', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0))),
% 0.76/0.94      inference('clc', [status(thm)], ['64', '66'])).
% 0.76/0.94  thf('70', plain,
% 0.76/0.94      (![X0 : $i, X2 : $i]: ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['68', '69'])).
% 0.76/0.94  thf('71', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['13', '70'])).
% 0.76/0.94  thf('72', plain,
% 0.76/0.94      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10))
% 0.76/0.94           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X8 @ X10)))),
% 0.76/0.94      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.76/0.94  thf('73', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X2) @ X1))
% 0.76/0.94           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['71', '72'])).
% 0.76/0.94  thf('74', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/0.94          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.94      inference('eq_fact', [status(thm)], ['7'])).
% 0.76/0.94  thf('75', plain,
% 0.76/0.94      (![X0 : $i, X2 : $i]: ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['68', '69'])).
% 0.76/0.94  thf('76', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X0 @ X0)
% 0.76/0.94           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.76/0.94      inference('sup-', [status(thm)], ['74', '75'])).
% 0.76/0.94  thf('77', plain,
% 0.76/0.94      (![X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.94           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('78', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X0 @ X0)
% 0.76/0.94           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.76/0.94      inference('sup+', [status(thm)], ['76', '77'])).
% 0.76/0.94  thf('79', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['13', '70'])).
% 0.76/0.94  thf('80', plain,
% 0.76/0.94      (![X15 : $i, X16 : $i]:
% 0.76/0.94         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.76/0.94           = (k3_xboole_0 @ X15 @ X16))),
% 0.76/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.94  thf('81', plain,
% 0.76/0.94      (![X11 : $i, X12 : $i]:
% 0.76/0.94         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.76/0.94           = (k2_xboole_0 @ X11 @ X12))),
% 0.76/0.94      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.94  thf('82', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.94           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.76/0.94      inference('sup+', [status(thm)], ['80', '81'])).
% 0.76/0.94  thf('83', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.94  thf('84', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.76/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.76/0.94  thf('85', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.94           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.76/0.94  thf('86', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.94           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.94      inference('demod', [status(thm)], ['3', '4'])).
% 0.76/0.94  thf('87', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.94           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.94      inference('sup+', [status(thm)], ['85', '86'])).
% 0.76/0.94  thf('88', plain,
% 0.76/0.94      (![X0 : $i, X1 : $i]:
% 0.76/0.94         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.76/0.94      inference('demod', [status(thm)], ['73', '78', '79', '87'])).
% 0.76/0.94  thf('89', plain, (((sk_A) != (sk_A))),
% 0.76/0.94      inference('demod', [status(thm)], ['6', '88'])).
% 0.76/0.94  thf('90', plain, ($false), inference('simplify', [status(thm)], ['89'])).
% 0.76/0.94  
% 0.76/0.94  % SZS output end Refutation
% 0.76/0.94  
% 0.76/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
