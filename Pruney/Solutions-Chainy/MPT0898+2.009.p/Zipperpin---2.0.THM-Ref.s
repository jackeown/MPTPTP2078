%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jfKlHzfixT

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:43 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 726 expanded)
%              Number of leaves         :   13 ( 212 expanded)
%              Depth                    :   29
%              Number of atoms          : 1025 (9569 expanded)
%              Number of equality atoms :  197 (1704 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

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

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('2',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( X13 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X13 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,
    ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      = sk_B )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = sk_B )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('18',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ( ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
        = ( k4_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ X0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( X9 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X13 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X10 @ X11 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','30'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('38',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('41',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('48',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('51',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('52',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X1 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('58',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X10 @ X11 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('59',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X10 @ X11 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ sk_B @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('70',plain,
    ( ( sk_B = sk_A )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A ) ),
    inference(demod,[status(thm)],['3','68','69'])).

thf('71',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
 != sk_A ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X10 @ X11 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('74',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('75',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('76',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ X10 @ X11 @ X13 )
      = sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['72','76'])).

thf('78',plain,(
    $false ),
    inference(simplify,[status(thm)],['77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jfKlHzfixT
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:24:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 120 iterations in 0.158s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.62  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.39/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.62  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.39/0.62  thf(t58_mcart_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.39/0.62       ( ( A ) = ( B ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i]:
% 0.39/0.62        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.39/0.62          ( ( A ) = ( B ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.39/0.62         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t55_mcart_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.62         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.39/0.62       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.62         (((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12) != (k1_xboole_0))
% 0.39/0.62          | ((X12) = (k1_xboole_0))
% 0.39/0.62          | ((X11) = (k1_xboole_0))
% 0.39/0.62          | ((X10) = (k1_xboole_0))
% 0.39/0.62          | ((X9) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      ((((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.39/0.62         (((X13) != (k1_xboole_0))
% 0.39/0.62          | ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X13) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.39/0.62  thf(d4_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.39/0.62       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.39/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.62  thf(t195_relat_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.62          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.39/0.62               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((X0) = (k1_xboole_0))
% 0.39/0.62          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 0.39/0.62          | ((X1) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.62         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 0.39/0.62          | ((X0) = (k1_xboole_0))
% 0.39/0.62          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.39/0.62         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.62         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 0.39/0.62          | ((X0) = (k1_xboole_0))
% 0.39/0.62          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      ((((k2_relat_1 @ (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)) = (sk_B))
% 0.39/0.62        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      ((((sk_A) = (sk_B))
% 0.39/0.62        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['8', '11'])).
% 0.39/0.62  thf('13', plain, (((sk_A) != (sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.39/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ X0)
% 0.39/0.62            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.39/0.62          | ((sk_B) = (k1_xboole_0))
% 0.39/0.62          | ((sk_A) = (k1_xboole_0))
% 0.39/0.62          | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      ((((k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.62        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['16', '17'])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.39/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ X0)
% 0.39/0.62            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.39/0.62          | ((sk_B) = (k1_xboole_0))
% 0.39/0.62          | ((sk_A) = (k1_xboole_0))
% 0.39/0.62          | ((k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      ((((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.39/0.62        | ((k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['5', '20'])).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      ((((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.62  thf(d3_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.39/0.62       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 0.39/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 0.39/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.39/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.39/0.62      inference('sup+', [status(thm)], ['23', '24'])).
% 0.39/0.62  thf('26', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.39/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.39/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.39/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.39/0.62            = (k4_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ X0))
% 0.39/0.62          | ((sk_A) = (k1_xboole_0))
% 0.39/0.62          | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['22', '27'])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.39/0.62         (((X9) != (k1_xboole_0))
% 0.39/0.62          | ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X13) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.39/0.62  thf('30', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ k1_xboole_0 @ X10 @ X11 @ X13) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.62          | ((sk_A) = (k1_xboole_0))
% 0.39/0.62          | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['28', '30'])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      ((((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 0.39/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k3_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.62            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.39/0.62          | ((sk_A) = (k1_xboole_0))
% 0.39/0.62          | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['32', '33'])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.39/0.62          | ((sk_B) = (k1_xboole_0))
% 0.39/0.62          | ((sk_A) = (k1_xboole_0))
% 0.39/0.62          | ((sk_B) = (k1_xboole_0))
% 0.39/0.62          | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['31', '34'])).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_A) = (k1_xboole_0))
% 0.39/0.62          | ((sk_B) = (k1_xboole_0))
% 0.39/0.62          | ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['35'])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ X0)
% 0.39/0.62            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.39/0.62          | ((sk_B) = (k1_xboole_0))
% 0.39/0.62          | ((sk_A) = (k1_xboole_0))
% 0.39/0.62          | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.39/0.62         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.39/0.62          = (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 0.39/0.62        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.62         (((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12) != (k1_xboole_0))
% 0.39/0.62          | ((X12) = (k1_xboole_0))
% 0.39/0.62          | ((X11) = (k1_xboole_0))
% 0.39/0.62          | ((X10) = (k1_xboole_0))
% 0.39/0.62          | ((X9) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['36', '42'])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.39/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ X0)
% 0.39/0.62            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.39/0.62          | ((sk_B) = (k1_xboole_0))
% 0.39/0.62          | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      ((((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      ((((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((k2_zfmisc_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.39/0.62           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 0.39/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0 @ X4)
% 0.39/0.62           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.39/0.62      inference('sup+', [status(thm)], ['51', '52'])).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ k1_xboole_0 @ X0)
% 0.39/0.62           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['50', '53'])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ k1_xboole_0 @ X0)
% 0.39/0.62           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['50', '53'])).
% 0.39/0.62  thf('56', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ X1)
% 0.39/0.62           = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['54', '55'])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.62         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.39/0.62           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.39/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.62  thf('58', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ k1_xboole_0 @ X10 @ X11 @ X13) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (![X1 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 0.39/0.62      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      ((((sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['49', '59'])).
% 0.39/0.62  thf('61', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['60'])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ k1_xboole_0 @ X10 @ X11 @ X13) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         (((k4_zfmisc_1 @ sk_B @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.62          | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['61', '62'])).
% 0.39/0.62  thf('64', plain,
% 0.39/0.62      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.39/0.62         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['63', '64'])).
% 0.39/0.62  thf('66', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.62         (((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12) != (k1_xboole_0))
% 0.39/0.62          | ((X12) = (k1_xboole_0))
% 0.39/0.62          | ((X11) = (k1_xboole_0))
% 0.39/0.62          | ((X10) = (k1_xboole_0))
% 0.39/0.62          | ((X9) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.39/0.62  thf('67', plain,
% 0.39/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0))
% 0.39/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['65', '66'])).
% 0.39/0.62  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['67'])).
% 0.39/0.62  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['67'])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      ((((sk_B) = (sk_A))
% 0.39/0.62        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['3', '68', '69'])).
% 0.39/0.62  thf('71', plain, (((sk_A) != (sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('72', plain, (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ k1_xboole_0 @ X10 @ X11 @ X13) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.62  thf('74', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['67'])).
% 0.39/0.62  thf('75', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['67'])).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.39/0.62         ((k4_zfmisc_1 @ sk_A @ X10 @ X11 @ X13) = (sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.39/0.62  thf('77', plain, (((sk_A) != (sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['72', '76'])).
% 0.39/0.62  thf('78', plain, ($false), inference('simplify', [status(thm)], ['77'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
