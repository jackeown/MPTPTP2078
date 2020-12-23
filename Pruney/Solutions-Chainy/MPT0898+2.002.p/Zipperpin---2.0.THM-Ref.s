%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xv2MKYDzSe

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:42 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 616 expanded)
%              Number of leaves         :   14 ( 183 expanded)
%              Depth                    :   23
%              Number of atoms          :  889 (7634 expanded)
%              Number of equality atoms :  135 (1019 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
        = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
          = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('0',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
      = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ X20 @ X21 )
      = ( k4_zfmisc_1 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('9',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ X4 @ X0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('23',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) )
      | ( r1_tarski @ X0 @ X4 )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) )
      | ( r1_tarski @ X0 @ X4 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['20','45'])).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('52',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A )
    | ( sk_B = sk_A )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A ) ),
    inference(demod,[status(thm)],['5','49','50','51'])).

thf('53',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','57'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('60',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['54','61'])).

thf('63',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_B )
    = sk_A ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('65',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = sk_A )
      | ( X4 = sk_A )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xv2MKYDzSe
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:58:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 176 iterations in 0.139s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.39/0.59  thf(t58_mcart_1, conjecture,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.39/0.59       ( ( A ) = ( B ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i]:
% 0.39/0.59        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.39/0.59          ( ( A ) = ( B ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.39/0.59         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t54_mcart_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D ) =
% 0.39/0.59       ( k4_zfmisc_1 @ A @ B @ C @ D ) ))).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.59         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19) @ X20 @ X21)
% 0.39/0.59           = (k4_zfmisc_1 @ X18 @ X19 @ X20 @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.39/0.59  thf(t35_mcart_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.59         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.39/0.59       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.59         (((k3_zfmisc_1 @ X14 @ X15 @ X16) != (k1_xboole_0))
% 0.39/0.59          | ((X16) = (k1_xboole_0))
% 0.39/0.59          | ((X15) = (k1_xboole_0))
% 0.39/0.59          | ((X14) = (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.39/0.59          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.39/0.59          | ((X1) = (k1_xboole_0))
% 0.39/0.59          | ((X0) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.39/0.59        | ((sk_B) = (k1_xboole_0))
% 0.39/0.59        | ((sk_B) = (k1_xboole_0))
% 0.39/0.59        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['0', '3'])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 0.39/0.59        | ((sk_B) = (k1_xboole_0))
% 0.39/0.59        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['4'])).
% 0.39/0.59  thf(d10_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.59  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.59  thf(d4_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.39/0.59       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.59         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.39/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.39/0.59         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.59         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.39/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.59  thf(t138_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.39/0.59       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.59         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.59         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.39/0.59          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.39/0.59          | (r1_tarski @ X7 @ X9))),
% 0.39/0.59      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k2_zfmisc_1 @ X5 @ X4) @ 
% 0.39/0.59             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.59          | (r1_tarski @ X4 @ X0)
% 0.39/0.59          | ((k2_zfmisc_1 @ X5 @ X4) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.39/0.59             (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.39/0.59          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.59          | (r1_tarski @ X0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['9', '12'])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.39/0.59             (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.39/0.59          | (r1_tarski @ X0 @ sk_B)
% 0.39/0.59          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '13'])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.59         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.39/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.39/0.59             (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.39/0.59          | (r1_tarski @ X0 @ sk_B)
% 0.39/0.59          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.59        | (r1_tarski @ sk_A @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['7', '16'])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.39/0.59          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.39/0.59          | ((X1) = (k1_xboole_0))
% 0.39/0.59          | ((X0) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.59        | (r1_tarski @ sk_A @ sk_B)
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | (r1_tarski @ sk_A @ sk_B))),
% 0.39/0.59      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.59  thf('21', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.59         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.39/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.39/0.59         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.59         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.39/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.59         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0))
% 0.39/0.59          | ~ (r1_tarski @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.39/0.59          | (r1_tarski @ X7 @ X9))),
% 0.39/0.59      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.39/0.59             (k2_zfmisc_1 @ X5 @ X4))
% 0.39/0.59          | (r1_tarski @ X0 @ X4)
% 0.39/0.59          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.59         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.39/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.39/0.59             (k2_zfmisc_1 @ X5 @ X4))
% 0.39/0.59          | (r1_tarski @ X0 @ X4)
% 0.39/0.59          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) @ 
% 0.39/0.59             (k2_zfmisc_1 @ X1 @ X0))
% 0.39/0.59          | ((k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B) = (k1_xboole_0))
% 0.39/0.59          | (r1_tarski @ sk_B @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['23', '28'])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.39/0.59         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) @ 
% 0.39/0.59             (k2_zfmisc_1 @ X1 @ X0))
% 0.39/0.59          | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.59          | (r1_tarski @ sk_B @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) @ 
% 0.39/0.59             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.59          | (r1_tarski @ sk_B @ X0)
% 0.39/0.59          | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['22', '31'])).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.59        | (r1_tarski @ sk_B @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['21', '32'])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.59         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.39/0.59           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.59  thf(t113_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]:
% 0.39/0.59         (((X3) = (k1_xboole_0))
% 0.39/0.59          | ((X4) = (k1_xboole_0))
% 0.39/0.59          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.39/0.59          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.39/0.59          | ((X0) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.59        | (r1_tarski @ sk_B @ sk_A)
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['33', '36'])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | (r1_tarski @ sk_B @ sk_A))),
% 0.39/0.59      inference('simplify', [status(thm)], ['37'])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.59         (((k3_zfmisc_1 @ X14 @ X15 @ X16) != (k1_xboole_0))
% 0.39/0.59          | ((X16) = (k1_xboole_0))
% 0.39/0.59          | ((X15) = (k1_xboole_0))
% 0.39/0.59          | ((X14) = (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.59        | (r1_tarski @ sk_B @ sk_A)
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.59  thf('41', plain, ((((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_A))),
% 0.39/0.59      inference('simplify', [status(thm)], ['40'])).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      (![X0 : $i, X2 : $i]:
% 0.39/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.59  thf('43', plain,
% 0.39/0.59      ((((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ~ (r1_tarski @ sk_A @ sk_B)
% 0.39/0.59        | ((sk_A) = (sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('44', plain, (((sk_A) != (sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('45', plain, ((((sk_A) = (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.39/0.59      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      ((((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('clc', [status(thm)], ['20', '45'])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]:
% 0.39/0.59         (((X3) = (k1_xboole_0))
% 0.39/0.59          | ((X4) = (k1_xboole_0))
% 0.39/0.59          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.60  thf('50', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.60  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.60  thf('52', plain,
% 0.39/0.60      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A))
% 0.39/0.60        | ((sk_B) = (sk_A))
% 0.39/0.60        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A)))),
% 0.39/0.60      inference('demod', [status(thm)], ['5', '49', '50', '51'])).
% 0.39/0.60  thf('53', plain, (((sk_A) != (sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('54', plain,
% 0.39/0.60      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A))
% 0.39/0.60        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A)))),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.39/0.60  thf('55', plain,
% 0.39/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.60         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.39/0.60           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.39/0.60      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.60  thf('56', plain,
% 0.39/0.60      (![X4 : $i, X5 : $i]:
% 0.39/0.60         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.60  thf('57', plain,
% 0.39/0.60      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['56'])).
% 0.39/0.60  thf('58', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['55', '57'])).
% 0.39/0.60  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.60  thf('60', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.60  thf('61', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A) = (sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.39/0.60  thf('62', plain,
% 0.39/0.60      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A)) | ((sk_A) != (sk_A)))),
% 0.39/0.60      inference('demod', [status(thm)], ['54', '61'])).
% 0.39/0.60  thf('63', plain, (((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A))),
% 0.39/0.60      inference('simplify', [status(thm)], ['62'])).
% 0.39/0.60  thf('64', plain,
% 0.39/0.60      (![X3 : $i, X4 : $i]:
% 0.39/0.60         (((X3) = (k1_xboole_0))
% 0.39/0.60          | ((X4) = (k1_xboole_0))
% 0.39/0.60          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.60  thf('65', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.60  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.60  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.60  thf('68', plain,
% 0.39/0.60      (![X3 : $i, X4 : $i]:
% 0.39/0.60         (((X3) = (sk_A))
% 0.39/0.60          | ((X4) = (sk_A))
% 0.39/0.60          | ((k2_zfmisc_1 @ X4 @ X3) != (sk_A)))),
% 0.39/0.60      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.39/0.60  thf('69', plain,
% 0.39/0.60      ((((sk_A) != (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['63', '68'])).
% 0.39/0.60  thf('70', plain, (((sk_B) = (sk_A))),
% 0.39/0.60      inference('simplify', [status(thm)], ['69'])).
% 0.39/0.60  thf('71', plain, (((sk_A) != (sk_B))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('72', plain, ($false),
% 0.39/0.60      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
