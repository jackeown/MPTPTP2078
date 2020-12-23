%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1g2k2ixSs6

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:43 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  104 (1419 expanded)
%              Number of leaves         :   13 ( 382 expanded)
%              Depth                    :   32
%              Number of atoms          :  988 (16748 expanded)
%              Number of equality atoms :  198 (3245 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( X12 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X10 @ X12 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X10 @ X12 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('7',plain,(
    ! [X9: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X9 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = X0 )
      | ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
        = ( k2_zfmisc_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X9 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('19',plain,
    ( ( k2_zfmisc_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X9 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('23',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','23'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      = sk_B )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A = sk_B )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','23'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X4 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ sk_A @ X0 )
      = sk_A ) ),
    inference(demod,[status(thm)],['24','56','57'])).

thf('59',plain,
    ( sk_A
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['1','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('61',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X5 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != sk_A )
      | ( X11 = sk_A )
      | ( X10 = sk_A )
      | ( X9 = sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != sk_A )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = sk_A )
      | ( X1 = sk_A )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A )
    | ( sk_B = sk_A ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_B @ sk_B @ X0 )
      = ( k2_zfmisc_1 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('79',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('81',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k2_zfmisc_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_zfmisc_1 @ sk_B @ sk_B @ X0 )
      = sk_A ) ),
    inference(demod,[status(thm)],['77','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
       != sk_A )
      | ( X11 = sk_A )
      | ( X10 = sk_A )
      | ( X9 = sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( sk_A != sk_A )
      | ( sk_B = sk_A )
      | ( sk_B = sk_A )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( sk_B = sk_A ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] : ( X0 = sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','87'])).

thf('89',plain,(
    $false ),
    inference(simplify,[status(thm)],['88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1g2k2ixSs6
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.00/1.22  % Solved by: fo/fo7.sh
% 1.00/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.22  % done 772 iterations in 0.775s
% 1.00/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.00/1.22  % SZS output start Refutation
% 1.00/1.22  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.00/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.22  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.00/1.22  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.00/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.22  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.00/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.22  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.00/1.22  thf(t58_mcart_1, conjecture,
% 1.00/1.22    (![A:$i,B:$i]:
% 1.00/1.22     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 1.00/1.22       ( ( A ) = ( B ) ) ))).
% 1.00/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.22    (~( ![A:$i,B:$i]:
% 1.00/1.22        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 1.00/1.22          ( ( A ) = ( B ) ) ) )),
% 1.00/1.22    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 1.00/1.22  thf('0', plain, (((sk_A) != (sk_B))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf('1', plain,
% 1.00/1.22      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 1.00/1.22         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf(t35_mcart_1, axiom,
% 1.00/1.22    (![A:$i,B:$i,C:$i]:
% 1.00/1.22     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.00/1.22         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 1.00/1.22       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 1.00/1.22  thf('2', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i, X12 : $i]:
% 1.00/1.22         (((X12) != (k1_xboole_0))
% 1.00/1.22          | ((k3_zfmisc_1 @ X9 @ X10 @ X12) = (k1_xboole_0)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.00/1.22  thf('3', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X9 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['2'])).
% 1.00/1.22  thf(d4_zfmisc_1, axiom,
% 1.00/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.22     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.00/1.22       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.00/1.22  thf('4', plain,
% 1.00/1.22      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.00/1.22         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 1.00/1.22           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 1.00/1.22      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.00/1.22  thf('5', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 1.00/1.22           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.00/1.22      inference('sup+', [status(thm)], ['3', '4'])).
% 1.00/1.22  thf('6', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i, X12 : $i]:
% 1.00/1.22         (((X10) != (k1_xboole_0))
% 1.00/1.22          | ((k3_zfmisc_1 @ X9 @ X10 @ X12) = (k1_xboole_0)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.00/1.22  thf('7', plain,
% 1.00/1.22      (![X9 : $i, X12 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X9 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['6'])).
% 1.00/1.22  thf(d3_zfmisc_1, axiom,
% 1.00/1.22    (![A:$i,B:$i,C:$i]:
% 1.00/1.22     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.00/1.22       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.00/1.22  thf('8', plain,
% 1.00/1.22      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.00/1.22           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.00/1.22      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.00/1.22  thf(t195_relat_1, axiom,
% 1.00/1.22    (![A:$i,B:$i]:
% 1.00/1.22     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.00/1.22          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 1.00/1.22               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 1.00/1.22  thf('9', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((X0) = (k1_xboole_0))
% 1.00/1.22          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 1.00/1.22          | ((X1) = (k1_xboole_0)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t195_relat_1])).
% 1.00/1.22  thf('10', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 1.00/1.22          | ((X0) = (k1_xboole_0))
% 1.00/1.22          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['8', '9'])).
% 1.00/1.22  thf('11', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((k2_relat_1 @ k1_xboole_0) = (X0))
% 1.00/1.22          | ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 1.00/1.22          | ((X0) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['7', '10'])).
% 1.00/1.22  thf('12', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((X0) != (k2_zfmisc_1 @ X1 @ k1_xboole_0))
% 1.00/1.22          | ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 1.00/1.22          | ((k2_relat_1 @ k1_xboole_0) = (X0)))),
% 1.00/1.22      inference('eq_fact', [status(thm)], ['11'])).
% 1.00/1.22  thf('13', plain,
% 1.00/1.22      (![X1 : $i]:
% 1.00/1.22         (((k2_relat_1 @ k1_xboole_0) = (k2_zfmisc_1 @ X1 @ k1_xboole_0))
% 1.00/1.22          | ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.00/1.22      inference('simplify', [status(thm)], ['12'])).
% 1.00/1.22  thf('14', plain,
% 1.00/1.22      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.00/1.22           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.00/1.22      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.00/1.22  thf('15', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 1.00/1.22            = (k2_zfmisc_1 @ (k2_relat_1 @ k1_xboole_0) @ X0))
% 1.00/1.22          | ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['13', '14'])).
% 1.00/1.22  thf('16', plain,
% 1.00/1.22      (![X9 : $i, X12 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X9 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['6'])).
% 1.00/1.22  thf('17', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((k1_xboole_0) = (k2_zfmisc_1 @ (k2_relat_1 @ k1_xboole_0) @ X0))
% 1.00/1.22          | ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.00/1.22      inference('demod', [status(thm)], ['15', '16'])).
% 1.00/1.22  thf('18', plain,
% 1.00/1.22      ((((k1_xboole_0) != (k1_xboole_0))
% 1.00/1.22        | ((k2_zfmisc_1 @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 1.00/1.22            = (k1_xboole_0)))),
% 1.00/1.22      inference('eq_fact', [status(thm)], ['17'])).
% 1.00/1.22  thf('19', plain,
% 1.00/1.22      (((k2_zfmisc_1 @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 1.00/1.22         = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['18'])).
% 1.00/1.22  thf('20', plain,
% 1.00/1.22      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.00/1.22           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.00/1.22      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.00/1.22  thf('21', plain,
% 1.00/1.22      (![X0 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0 @ X0)
% 1.00/1.22           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.00/1.22      inference('sup+', [status(thm)], ['19', '20'])).
% 1.00/1.22  thf('22', plain,
% 1.00/1.22      (![X9 : $i, X12 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X9 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['6'])).
% 1.00/1.22  thf('23', plain,
% 1.00/1.22      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.00/1.22      inference('demod', [status(thm)], ['21', '22'])).
% 1.00/1.22  thf('24', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.00/1.22      inference('demod', [status(thm)], ['5', '23'])).
% 1.00/1.22  thf('25', plain,
% 1.00/1.22      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.00/1.22         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 1.00/1.22           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 1.00/1.22      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.00/1.22  thf('26', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((X0) = (k1_xboole_0))
% 1.00/1.22          | ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X1))
% 1.00/1.22          | ((X1) = (k1_xboole_0)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t195_relat_1])).
% 1.00/1.22  thf('27', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.00/1.22         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 1.00/1.22          | ((X0) = (k1_xboole_0))
% 1.00/1.22          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['25', '26'])).
% 1.00/1.22  thf('28', plain,
% 1.00/1.22      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 1.00/1.22         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf('29', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.00/1.22         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 1.00/1.22          | ((X0) = (k1_xboole_0))
% 1.00/1.22          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['25', '26'])).
% 1.00/1.22  thf('30', plain,
% 1.00/1.22      ((((k2_relat_1 @ (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)) = (sk_B))
% 1.00/1.22        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0))
% 1.00/1.22        | ((sk_B) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['28', '29'])).
% 1.00/1.22  thf('31', plain,
% 1.00/1.22      ((((sk_A) = (sk_B))
% 1.00/1.22        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_B) = (k1_xboole_0))
% 1.00/1.22        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['27', '30'])).
% 1.00/1.22  thf('32', plain, (((sk_A) != (sk_B))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf('33', plain,
% 1.00/1.22      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_B) = (k1_xboole_0))
% 1.00/1.22        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0)))),
% 1.00/1.22      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 1.00/1.22  thf('34', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.22         (((k3_zfmisc_1 @ X9 @ X10 @ X11) != (k1_xboole_0))
% 1.00/1.22          | ((X11) = (k1_xboole_0))
% 1.00/1.22          | ((X10) = (k1_xboole_0))
% 1.00/1.22          | ((X9) = (k1_xboole_0)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.00/1.22  thf('35', plain,
% 1.00/1.22      ((((k1_xboole_0) != (k1_xboole_0))
% 1.00/1.22        | ((sk_B) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_B) = (k1_xboole_0))
% 1.00/1.22        | ((sk_B) = (k1_xboole_0))
% 1.00/1.22        | ((sk_B) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.22  thf('36', plain,
% 1.00/1.22      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_B) = (k1_xboole_0)))),
% 1.00/1.22      inference('simplify', [status(thm)], ['35'])).
% 1.00/1.22  thf('37', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.22         (((k3_zfmisc_1 @ X9 @ X10 @ X11) != (k1_xboole_0))
% 1.00/1.22          | ((X11) = (k1_xboole_0))
% 1.00/1.22          | ((X10) = (k1_xboole_0))
% 1.00/1.22          | ((X9) = (k1_xboole_0)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.00/1.22  thf('38', plain,
% 1.00/1.22      ((((k1_xboole_0) != (k1_xboole_0))
% 1.00/1.22        | ((sk_B) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['36', '37'])).
% 1.00/1.22  thf('39', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 1.00/1.22      inference('simplify', [status(thm)], ['38'])).
% 1.00/1.22  thf('40', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.00/1.22      inference('demod', [status(thm)], ['5', '23'])).
% 1.00/1.22  thf('41', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (((k4_zfmisc_1 @ X2 @ X1 @ sk_B @ X0) = (k1_xboole_0))
% 1.00/1.22          | ((sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['39', '40'])).
% 1.00/1.22  thf('42', plain,
% 1.00/1.22      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 1.00/1.22         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf('43', plain,
% 1.00/1.22      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['41', '42'])).
% 1.00/1.22  thf('44', plain,
% 1.00/1.22      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.00/1.22         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 1.00/1.22           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 1.00/1.22      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.00/1.22  thf('45', plain,
% 1.00/1.22      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.00/1.22           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.00/1.22      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.00/1.22  thf('46', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0 @ X4)
% 1.00/1.22           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 1.00/1.22      inference('sup+', [status(thm)], ['44', '45'])).
% 1.00/1.22  thf('47', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.22         (((k3_zfmisc_1 @ X9 @ X10 @ X11) != (k1_xboole_0))
% 1.00/1.22          | ((X11) = (k1_xboole_0))
% 1.00/1.22          | ((X10) = (k1_xboole_0))
% 1.00/1.22          | ((X9) = (k1_xboole_0)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.00/1.22  thf('48', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.22         (((k2_zfmisc_1 @ (k4_zfmisc_1 @ X4 @ X3 @ X2 @ X1) @ X0)
% 1.00/1.22            != (k1_xboole_0))
% 1.00/1.22          | ((k3_zfmisc_1 @ X4 @ X3 @ X2) = (k1_xboole_0))
% 1.00/1.22          | ((X1) = (k1_xboole_0))
% 1.00/1.22          | ((X0) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['46', '47'])).
% 1.00/1.22  thf('49', plain,
% 1.00/1.22      (![X0 : $i]:
% 1.00/1.22         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.00/1.22          | ((sk_A) = (k1_xboole_0))
% 1.00/1.22          | ((X0) = (k1_xboole_0))
% 1.00/1.22          | ((sk_A) = (k1_xboole_0))
% 1.00/1.22          | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['43', '48'])).
% 1.00/1.22  thf('50', plain,
% 1.00/1.22      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.00/1.22      inference('demod', [status(thm)], ['21', '22'])).
% 1.00/1.22  thf('51', plain,
% 1.00/1.22      (![X0 : $i]:
% 1.00/1.22         (((k1_xboole_0) != (k1_xboole_0))
% 1.00/1.22          | ((sk_A) = (k1_xboole_0))
% 1.00/1.22          | ((X0) = (k1_xboole_0))
% 1.00/1.22          | ((sk_A) = (k1_xboole_0))
% 1.00/1.22          | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('demod', [status(thm)], ['49', '50'])).
% 1.00/1.22  thf('52', plain,
% 1.00/1.22      (![X0 : $i]:
% 1.00/1.22         (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 1.00/1.22          | ((X0) = (k1_xboole_0))
% 1.00/1.22          | ((sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('simplify', [status(thm)], ['51'])).
% 1.00/1.22  thf('53', plain,
% 1.00/1.22      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('condensation', [status(thm)], ['52'])).
% 1.00/1.22  thf('54', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.22         (((k3_zfmisc_1 @ X9 @ X10 @ X11) != (k1_xboole_0))
% 1.00/1.22          | ((X11) = (k1_xboole_0))
% 1.00/1.22          | ((X10) = (k1_xboole_0))
% 1.00/1.22          | ((X9) = (k1_xboole_0)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.00/1.22  thf('55', plain,
% 1.00/1.22      ((((k1_xboole_0) != (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['53', '54'])).
% 1.00/1.22  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['55'])).
% 1.00/1.22  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['55'])).
% 1.00/1.22  thf('58', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         ((k4_zfmisc_1 @ X2 @ X1 @ sk_A @ X0) = (sk_A))),
% 1.00/1.22      inference('demod', [status(thm)], ['24', '56', '57'])).
% 1.00/1.22  thf('59', plain, (((sk_A) = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 1.00/1.22      inference('demod', [status(thm)], ['1', '58'])).
% 1.00/1.22  thf('60', plain,
% 1.00/1.22      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.00/1.22           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.00/1.22      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.00/1.22  thf('61', plain,
% 1.00/1.22      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.00/1.22           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.00/1.22      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.00/1.22  thf('62', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.00/1.22           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 1.00/1.22      inference('sup+', [status(thm)], ['60', '61'])).
% 1.00/1.22  thf('63', plain,
% 1.00/1.22      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.00/1.22         ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 1.00/1.22           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X5 @ X6 @ X7) @ X8))),
% 1.00/1.22      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.00/1.22  thf('64', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.00/1.22           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.00/1.22      inference('demod', [status(thm)], ['62', '63'])).
% 1.00/1.22  thf('65', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.22         (((k3_zfmisc_1 @ X9 @ X10 @ X11) != (k1_xboole_0))
% 1.00/1.22          | ((X11) = (k1_xboole_0))
% 1.00/1.22          | ((X10) = (k1_xboole_0))
% 1.00/1.22          | ((X9) = (k1_xboole_0)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.00/1.22  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['55'])).
% 1.00/1.22  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['55'])).
% 1.00/1.22  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['55'])).
% 1.00/1.22  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['55'])).
% 1.00/1.22  thf('70', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.22         (((k3_zfmisc_1 @ X9 @ X10 @ X11) != (sk_A))
% 1.00/1.22          | ((X11) = (sk_A))
% 1.00/1.22          | ((X10) = (sk_A))
% 1.00/1.22          | ((X9) = (sk_A)))),
% 1.00/1.22      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 1.00/1.22  thf('71', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.00/1.22         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (sk_A))
% 1.00/1.22          | ((k2_zfmisc_1 @ X3 @ X2) = (sk_A))
% 1.00/1.22          | ((X1) = (sk_A))
% 1.00/1.22          | ((X0) = (sk_A)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['64', '70'])).
% 1.00/1.22  thf('72', plain,
% 1.00/1.22      ((((sk_A) != (sk_A))
% 1.00/1.22        | ((sk_B) = (sk_A))
% 1.00/1.22        | ((sk_B) = (sk_A))
% 1.00/1.22        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['59', '71'])).
% 1.00/1.22  thf('73', plain,
% 1.00/1.22      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 1.00/1.22      inference('simplify', [status(thm)], ['72'])).
% 1.00/1.22  thf('74', plain, (((sk_A) != (sk_B))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf('75', plain, (((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A))),
% 1.00/1.22      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 1.00/1.22  thf('76', plain,
% 1.00/1.22      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ X2 @ X3 @ X4)
% 1.00/1.22           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3) @ X4))),
% 1.00/1.22      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.00/1.22  thf('77', plain,
% 1.00/1.22      (![X0 : $i]:
% 1.00/1.22         ((k3_zfmisc_1 @ sk_B @ sk_B @ X0) = (k2_zfmisc_1 @ sk_A @ X0))),
% 1.00/1.22      inference('sup+', [status(thm)], ['75', '76'])).
% 1.00/1.22  thf('78', plain,
% 1.00/1.22      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.00/1.22      inference('demod', [status(thm)], ['21', '22'])).
% 1.00/1.22  thf('79', plain, (((sk_A) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['55'])).
% 1.00/1.22  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['55'])).
% 1.00/1.22  thf('81', plain, (![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ sk_A @ X0))),
% 1.00/1.22      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.00/1.22  thf('82', plain, (![X0 : $i]: ((k3_zfmisc_1 @ sk_B @ sk_B @ X0) = (sk_A))),
% 1.00/1.22      inference('demod', [status(thm)], ['77', '81'])).
% 1.00/1.22  thf('83', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.22         (((k3_zfmisc_1 @ X9 @ X10 @ X11) != (sk_A))
% 1.00/1.22          | ((X11) = (sk_A))
% 1.00/1.22          | ((X10) = (sk_A))
% 1.00/1.22          | ((X9) = (sk_A)))),
% 1.00/1.22      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 1.00/1.22  thf('84', plain,
% 1.00/1.22      (![X0 : $i]:
% 1.00/1.22         (((sk_A) != (sk_A))
% 1.00/1.22          | ((sk_B) = (sk_A))
% 1.00/1.22          | ((sk_B) = (sk_A))
% 1.00/1.22          | ((X0) = (sk_A)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['82', '83'])).
% 1.00/1.22  thf('85', plain, (![X0 : $i]: (((X0) = (sk_A)) | ((sk_B) = (sk_A)))),
% 1.00/1.22      inference('simplify', [status(thm)], ['84'])).
% 1.00/1.22  thf('86', plain, (((sk_A) != (sk_B))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf('87', plain, (![X0 : $i]: ((X0) = (sk_A))),
% 1.00/1.22      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 1.00/1.22  thf('88', plain, (((sk_A) != (sk_A))),
% 1.00/1.22      inference('demod', [status(thm)], ['0', '87'])).
% 1.00/1.22  thf('89', plain, ($false), inference('simplify', [status(thm)], ['88'])).
% 1.00/1.22  
% 1.00/1.22  % SZS output end Refutation
% 1.00/1.22  
% 1.04/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
