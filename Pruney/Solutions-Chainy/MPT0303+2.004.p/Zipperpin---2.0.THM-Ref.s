%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FCEuWlqeQE

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:10 EST 2020

% Result     : Theorem 5.51s
% Output     : Refutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 568 expanded)
%              Number of leaves         :   14 ( 161 expanded)
%              Depth                    :   19
%              Number of atoms          :  831 (6502 expanded)
%              Number of equality atoms :   52 ( 393 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X16 ) )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t115_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ A )
        = ( k2_zfmisc_1 @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ A )
          = ( k2_zfmisc_1 @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t115_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_A )
    = ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(condensation,[status(thm)],['8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','37','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','46'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X16 ) )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D @ sk_B @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ ( sk_D @ sk_B @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_A )
    = ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ ( sk_D @ sk_B @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('59',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('61',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('63',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('68',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['61','62','63','68'])).

thf('70',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FCEuWlqeQE
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 5.51/5.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.51/5.71  % Solved by: fo/fo7.sh
% 5.51/5.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.51/5.71  % done 3614 iterations in 5.256s
% 5.51/5.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.51/5.71  % SZS output start Refutation
% 5.51/5.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.51/5.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.51/5.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.51/5.71  thf(sk_B_type, type, sk_B: $i).
% 5.51/5.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.51/5.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.51/5.71  thf(sk_A_type, type, sk_A: $i).
% 5.51/5.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.51/5.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 5.51/5.71  thf(d3_tarski, axiom,
% 5.51/5.71    (![A:$i,B:$i]:
% 5.51/5.71     ( ( r1_tarski @ A @ B ) <=>
% 5.51/5.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.51/5.71  thf('0', plain,
% 5.51/5.71      (![X1 : $i, X3 : $i]:
% 5.51/5.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.51/5.71      inference('cnf', [status(esa)], [d3_tarski])).
% 5.51/5.71  thf('1', plain,
% 5.51/5.71      (![X1 : $i, X3 : $i]:
% 5.51/5.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.51/5.71      inference('cnf', [status(esa)], [d3_tarski])).
% 5.51/5.71  thf(l54_zfmisc_1, axiom,
% 5.51/5.71    (![A:$i,B:$i,C:$i,D:$i]:
% 5.51/5.71     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 5.51/5.71       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 5.51/5.71  thf('2', plain,
% 5.51/5.71      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 5.51/5.71         ((r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X16))
% 5.51/5.71          | ~ (r2_hidden @ X14 @ X16)
% 5.51/5.71          | ~ (r2_hidden @ X12 @ X13))),
% 5.51/5.71      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 5.51/5.71  thf('3', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.51/5.71         ((r1_tarski @ X0 @ X1)
% 5.51/5.71          | ~ (r2_hidden @ X3 @ X2)
% 5.51/5.71          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 5.51/5.71             (k2_zfmisc_1 @ X2 @ X0)))),
% 5.51/5.71      inference('sup-', [status(thm)], ['1', '2'])).
% 5.51/5.71  thf('4', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.51/5.71         ((r1_tarski @ X0 @ X1)
% 5.51/5.71          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 5.51/5.71             (k2_zfmisc_1 @ X0 @ X2))
% 5.51/5.71          | (r1_tarski @ X2 @ X3))),
% 5.51/5.71      inference('sup-', [status(thm)], ['0', '3'])).
% 5.51/5.71  thf(t115_zfmisc_1, conjecture,
% 5.51/5.71    (![A:$i,B:$i]:
% 5.51/5.71     ( ( ( k2_zfmisc_1 @ A @ A ) = ( k2_zfmisc_1 @ B @ B ) ) =>
% 5.51/5.71       ( ( A ) = ( B ) ) ))).
% 5.51/5.71  thf(zf_stmt_0, negated_conjecture,
% 5.51/5.71    (~( ![A:$i,B:$i]:
% 5.51/5.71        ( ( ( k2_zfmisc_1 @ A @ A ) = ( k2_zfmisc_1 @ B @ B ) ) =>
% 5.51/5.71          ( ( A ) = ( B ) ) ) )),
% 5.51/5.71    inference('cnf.neg', [status(esa)], [t115_zfmisc_1])).
% 5.51/5.71  thf('5', plain,
% 5.51/5.71      (((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_zfmisc_1 @ sk_B @ sk_B))),
% 5.51/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.71  thf('6', plain,
% 5.51/5.71      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.71         ((r2_hidden @ X12 @ X13)
% 5.51/5.71          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X15)))),
% 5.51/5.71      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 5.51/5.71  thf('7', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 5.51/5.71          | (r2_hidden @ X1 @ sk_B))),
% 5.51/5.71      inference('sup-', [status(thm)], ['5', '6'])).
% 5.51/5.71  thf('8', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         ((r1_tarski @ sk_A @ X0)
% 5.51/5.71          | (r1_tarski @ sk_A @ X1)
% 5.51/5.71          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B))),
% 5.51/5.71      inference('sup-', [status(thm)], ['4', '7'])).
% 5.51/5.71  thf('9', plain,
% 5.51/5.71      (![X0 : $i]:
% 5.51/5.71         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B) | (r1_tarski @ sk_A @ X0))),
% 5.51/5.71      inference('condensation', [status(thm)], ['8'])).
% 5.51/5.71  thf('10', plain,
% 5.51/5.71      (![X1 : $i, X3 : $i]:
% 5.51/5.71         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.51/5.71      inference('cnf', [status(esa)], [d3_tarski])).
% 5.51/5.71  thf('11', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 5.51/5.71      inference('sup-', [status(thm)], ['9', '10'])).
% 5.51/5.71  thf('12', plain, ((r1_tarski @ sk_A @ sk_B)),
% 5.51/5.71      inference('simplify', [status(thm)], ['11'])).
% 5.51/5.71  thf(t28_xboole_1, axiom,
% 5.51/5.71    (![A:$i,B:$i]:
% 5.51/5.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.51/5.71  thf('13', plain,
% 5.51/5.71      (![X10 : $i, X11 : $i]:
% 5.51/5.71         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 5.51/5.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.51/5.71  thf('14', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 5.51/5.71      inference('sup-', [status(thm)], ['12', '13'])).
% 5.51/5.71  thf(d4_xboole_0, axiom,
% 5.51/5.71    (![A:$i,B:$i,C:$i]:
% 5.51/5.71     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 5.51/5.71       ( ![D:$i]:
% 5.51/5.71         ( ( r2_hidden @ D @ C ) <=>
% 5.51/5.71           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.51/5.71  thf('15', plain,
% 5.51/5.71      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.51/5.71         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 5.51/5.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 5.51/5.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.51/5.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.51/5.71  thf('16', plain,
% 5.51/5.71      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.51/5.71         (~ (r2_hidden @ X8 @ X7)
% 5.51/5.71          | (r2_hidden @ X8 @ X6)
% 5.51/5.71          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 5.51/5.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.51/5.71  thf('17', plain,
% 5.51/5.71      (![X5 : $i, X6 : $i, X8 : $i]:
% 5.51/5.71         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 5.51/5.71      inference('simplify', [status(thm)], ['16'])).
% 5.51/5.71  thf('18', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.51/5.71         ((r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X3)
% 5.51/5.71          | ((X3) = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 5.51/5.71          | (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 5.51/5.71      inference('sup-', [status(thm)], ['15', '17'])).
% 5.51/5.71  thf('19', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.51/5.71         ((r2_hidden @ (sk_D @ X0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X0)
% 5.51/5.71          | ((X0) = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))))),
% 5.51/5.71      inference('eq_fact', [status(thm)], ['18'])).
% 5.51/5.71  thf('20', plain,
% 5.51/5.71      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.51/5.71         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 5.51/5.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 5.51/5.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.51/5.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.51/5.71  thf('21', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.51/5.71          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.51/5.71      inference('eq_fact', [status(thm)], ['20'])).
% 5.51/5.71  thf('22', plain,
% 5.51/5.71      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 5.51/5.71         (~ (r2_hidden @ X4 @ X5)
% 5.51/5.71          | ~ (r2_hidden @ X4 @ X6)
% 5.51/5.71          | (r2_hidden @ X4 @ X7)
% 5.51/5.71          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 5.51/5.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.51/5.71  thf('23', plain,
% 5.51/5.71      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.51/5.71         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 5.51/5.71          | ~ (r2_hidden @ X4 @ X6)
% 5.51/5.71          | ~ (r2_hidden @ X4 @ X5))),
% 5.51/5.71      inference('simplify', [status(thm)], ['22'])).
% 5.51/5.71  thf('24', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.51/5.71         (((X0) = (k3_xboole_0 @ X0 @ X1))
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2)
% 5.51/5.71          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 5.51/5.71      inference('sup-', [status(thm)], ['21', '23'])).
% 5.51/5.71  thf('25', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         (((X0) = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 5.51/5.71          | (r2_hidden @ (sk_D @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ 
% 5.51/5.71             (k3_xboole_0 @ X0 @ X0))
% 5.51/5.71          | ((X0) = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 5.51/5.71      inference('sup-', [status(thm)], ['19', '24'])).
% 5.51/5.71  thf('26', plain,
% 5.51/5.71      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.51/5.71         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 5.51/5.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 5.51/5.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.51/5.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.51/5.71  thf('27', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.51/5.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.51/5.71      inference('eq_fact', [status(thm)], ['26'])).
% 5.51/5.71  thf('28', plain,
% 5.51/5.71      (![X5 : $i, X6 : $i, X8 : $i]:
% 5.51/5.71         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 5.51/5.71      inference('simplify', [status(thm)], ['16'])).
% 5.51/5.71  thf('29', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.51/5.71         (((k3_xboole_0 @ X1 @ X0)
% 5.51/5.71            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 5.51/5.71          | (r2_hidden @ 
% 5.51/5.71             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 5.51/5.71             X0))),
% 5.51/5.71      inference('sup-', [status(thm)], ['27', '28'])).
% 5.51/5.71  thf('30', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.51/5.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.51/5.71      inference('eq_fact', [status(thm)], ['26'])).
% 5.51/5.71  thf('31', plain,
% 5.51/5.71      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.51/5.71         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.51/5.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.51/5.71  thf('32', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 5.51/5.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.51/5.71      inference('sup-', [status(thm)], ['30', '31'])).
% 5.51/5.71  thf('33', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.51/5.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.51/5.71      inference('simplify', [status(thm)], ['32'])).
% 5.51/5.71  thf('34', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.51/5.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.51/5.71      inference('eq_fact', [status(thm)], ['26'])).
% 5.51/5.71  thf('35', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 5.51/5.71      inference('clc', [status(thm)], ['33', '34'])).
% 5.51/5.71  thf('36', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         (((k3_xboole_0 @ X1 @ X0)
% 5.51/5.71            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 5.51/5.71          | ((k3_xboole_0 @ X1 @ X0)
% 5.51/5.71              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 5.51/5.71      inference('sup-', [status(thm)], ['29', '35'])).
% 5.51/5.71  thf('37', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         ((k3_xboole_0 @ X1 @ X0)
% 5.51/5.71           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.51/5.71      inference('simplify', [status(thm)], ['36'])).
% 5.51/5.71  thf('38', plain,
% 5.51/5.71      (![X1 : $i, X3 : $i]:
% 5.51/5.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.51/5.71      inference('cnf', [status(esa)], [d3_tarski])).
% 5.51/5.71  thf('39', plain,
% 5.51/5.71      (![X1 : $i, X3 : $i]:
% 5.51/5.71         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.51/5.71      inference('cnf', [status(esa)], [d3_tarski])).
% 5.51/5.71  thf('40', plain,
% 5.51/5.71      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 5.51/5.71      inference('sup-', [status(thm)], ['38', '39'])).
% 5.51/5.71  thf('41', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 5.51/5.71      inference('simplify', [status(thm)], ['40'])).
% 5.51/5.71  thf('42', plain,
% 5.51/5.71      (![X10 : $i, X11 : $i]:
% 5.51/5.71         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 5.51/5.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.51/5.71  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 5.51/5.71      inference('sup-', [status(thm)], ['41', '42'])).
% 5.51/5.71  thf('44', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         ((k3_xboole_0 @ X1 @ X0)
% 5.51/5.71           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.51/5.71      inference('simplify', [status(thm)], ['36'])).
% 5.51/5.71  thf('45', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 5.51/5.71          | (r2_hidden @ (sk_D @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ X0)
% 5.51/5.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.51/5.71      inference('demod', [status(thm)], ['25', '37', '43', '44'])).
% 5.51/5.71  thf('46', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         ((r2_hidden @ (sk_D @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ X0)
% 5.51/5.71          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.51/5.71      inference('simplify', [status(thm)], ['45'])).
% 5.51/5.71  thf('47', plain,
% 5.51/5.71      (((r2_hidden @ (sk_D @ sk_B @ sk_A @ sk_B) @ sk_B)
% 5.51/5.71        | ((sk_B) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 5.51/5.71      inference('sup+', [status(thm)], ['14', '46'])).
% 5.51/5.71  thf('48', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 5.51/5.71      inference('sup-', [status(thm)], ['12', '13'])).
% 5.51/5.71  thf('49', plain,
% 5.51/5.71      (((r2_hidden @ (sk_D @ sk_B @ sk_A @ sk_B) @ sk_B) | ((sk_B) = (sk_A)))),
% 5.51/5.71      inference('demod', [status(thm)], ['47', '48'])).
% 5.51/5.71  thf('50', plain, (((sk_A) != (sk_B))),
% 5.51/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.71  thf('51', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_A @ sk_B) @ sk_B)),
% 5.51/5.71      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 5.51/5.71  thf('52', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_A @ sk_B) @ sk_B)),
% 5.51/5.71      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 5.51/5.71  thf('53', plain,
% 5.51/5.71      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 5.51/5.71         ((r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X16))
% 5.51/5.71          | ~ (r2_hidden @ X14 @ X16)
% 5.51/5.71          | ~ (r2_hidden @ X12 @ X13))),
% 5.51/5.71      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 5.51/5.71  thf('54', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         (~ (r2_hidden @ X1 @ X0)
% 5.51/5.71          | (r2_hidden @ (k4_tarski @ X1 @ (sk_D @ sk_B @ sk_A @ sk_B)) @ 
% 5.51/5.71             (k2_zfmisc_1 @ X0 @ sk_B)))),
% 5.51/5.71      inference('sup-', [status(thm)], ['52', '53'])).
% 5.51/5.71  thf('55', plain,
% 5.51/5.71      ((r2_hidden @ 
% 5.51/5.71        (k4_tarski @ (sk_D @ sk_B @ sk_A @ sk_B) @ (sk_D @ sk_B @ sk_A @ sk_B)) @ 
% 5.51/5.71        (k2_zfmisc_1 @ sk_B @ sk_B))),
% 5.51/5.71      inference('sup-', [status(thm)], ['51', '54'])).
% 5.51/5.71  thf('56', plain,
% 5.51/5.71      (((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_zfmisc_1 @ sk_B @ sk_B))),
% 5.51/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.71  thf('57', plain,
% 5.51/5.71      ((r2_hidden @ 
% 5.51/5.71        (k4_tarski @ (sk_D @ sk_B @ sk_A @ sk_B) @ (sk_D @ sk_B @ sk_A @ sk_B)) @ 
% 5.51/5.71        (k2_zfmisc_1 @ sk_A @ sk_A))),
% 5.51/5.71      inference('demod', [status(thm)], ['55', '56'])).
% 5.51/5.71  thf('58', plain,
% 5.51/5.71      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.51/5.71         ((r2_hidden @ X12 @ X13)
% 5.51/5.71          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X15)))),
% 5.51/5.71      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 5.51/5.71  thf('59', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_A @ sk_B) @ sk_A)),
% 5.51/5.71      inference('sup-', [status(thm)], ['57', '58'])).
% 5.51/5.71  thf('60', plain,
% 5.51/5.71      (![X5 : $i, X6 : $i, X9 : $i]:
% 5.51/5.71         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 5.51/5.71          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 5.51/5.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.51/5.71  thf('61', plain,
% 5.51/5.71      ((~ (r2_hidden @ (sk_D @ sk_B @ sk_A @ sk_B) @ sk_B)
% 5.51/5.71        | ~ (r2_hidden @ (sk_D @ sk_B @ sk_A @ sk_B) @ sk_B)
% 5.51/5.71        | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 5.51/5.71      inference('sup-', [status(thm)], ['59', '60'])).
% 5.51/5.71  thf('62', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_A @ sk_B) @ sk_B)),
% 5.51/5.71      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 5.51/5.71  thf('63', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_A @ sk_B) @ sk_B)),
% 5.51/5.71      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 5.51/5.71  thf('64', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 5.51/5.71      inference('sup-', [status(thm)], ['12', '13'])).
% 5.51/5.71  thf('65', plain,
% 5.51/5.71      (![X0 : $i, X1 : $i]:
% 5.51/5.71         ((k3_xboole_0 @ X1 @ X0)
% 5.51/5.71           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.51/5.71      inference('simplify', [status(thm)], ['36'])).
% 5.51/5.71  thf('66', plain,
% 5.51/5.71      (((k3_xboole_0 @ sk_A @ sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 5.51/5.71      inference('sup+', [status(thm)], ['64', '65'])).
% 5.51/5.71  thf('67', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 5.51/5.71      inference('sup-', [status(thm)], ['12', '13'])).
% 5.51/5.71  thf('68', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 5.51/5.71      inference('demod', [status(thm)], ['66', '67'])).
% 5.51/5.71  thf('69', plain, (((sk_B) = (sk_A))),
% 5.51/5.71      inference('demod', [status(thm)], ['61', '62', '63', '68'])).
% 5.51/5.71  thf('70', plain, (((sk_A) != (sk_B))),
% 5.51/5.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.71  thf('71', plain, ($false),
% 5.51/5.71      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 5.51/5.71  
% 5.51/5.71  % SZS output end Refutation
% 5.51/5.71  
% 5.51/5.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
