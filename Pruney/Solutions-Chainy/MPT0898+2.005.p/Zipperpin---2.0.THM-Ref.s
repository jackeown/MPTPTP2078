%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PNJyVXimTA

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:42 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 822 expanded)
%              Number of leaves         :   13 ( 239 expanded)
%              Depth                    :   31
%              Number of atoms          :  823 (10015 expanded)
%              Number of equality atoms :  181 (2054 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X8 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X8 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
        = X4 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('10',plain,
    ( ( ( k2_relat_1 @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      = sk_B )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_A = sk_B )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X8 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','31'])).

thf('33',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('45',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('46',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A )
    | ( sk_B = sk_A )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['4','43','44','45'])).

thf('47',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('50',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( sk_A != sk_A )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['48','52'])).

thf('54',plain,
    ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
    = sk_A ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('58',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != sk_A )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = sk_A )
      | ( X0 = sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = sk_A )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A )
    | ( sk_B = sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('65',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_A )
      | ( X1 = sk_A )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PNJyVXimTA
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 168 iterations in 0.088s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.19/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.52  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.19/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.52  thf(t58_mcart_1, conjecture,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.19/0.52       ( ( A ) = ( B ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i]:
% 0.19/0.52        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.19/0.52          ( ( A ) = ( B ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.19/0.52         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d4_zfmisc_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.52     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.19/0.52       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.52         ((k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11)
% 0.19/0.52           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X8 @ X9 @ X10) @ X11))),
% 0.19/0.52      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.19/0.52  thf(t113_zfmisc_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X0) = (k1_xboole_0))
% 0.19/0.52          | ((X1) = (k1_xboole_0))
% 0.19/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.52         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.19/0.52          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.19/0.52          | ((X0) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.52         ((k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11)
% 0.19/0.52           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X8 @ X9 @ X10) @ X11))),
% 0.19/0.52      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.19/0.52  thf(t195_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.52          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.19/0.52               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X3 : $i, X4 : $i]:
% 0.19/0.52         (((X3) = (k1_xboole_0))
% 0.19/0.52          | ((k2_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X4))
% 0.19/0.52          | ((X4) = (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.52         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 0.19/0.52          | ((X0) = (k1_xboole_0))
% 0.19/0.52          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.19/0.52         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.52         (((k2_relat_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)) = (X0))
% 0.19/0.52          | ((X0) = (k1_xboole_0))
% 0.19/0.52          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      ((((k2_relat_1 @ (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)) = (sk_B))
% 0.19/0.52        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      ((((sk_A) = (sk_B))
% 0.19/0.52        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['7', '10'])).
% 0.19/0.52  thf('12', plain, (((sk_A) != (sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.19/0.52  thf(d3_zfmisc_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.19/0.52       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.52         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.19/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.19/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X0) = (k1_xboole_0))
% 0.19/0.52          | ((X1) = (k1_xboole_0))
% 0.19/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.19/0.52          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.19/0.52          | ((X0) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.19/0.52          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.19/0.52          | ((X0) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X0) = (k1_xboole_0))
% 0.19/0.52          | ((X1) = (k1_xboole_0))
% 0.19/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.52  thf('24', plain,
% 0.19/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X0) = (k1_xboole_0))
% 0.19/0.52          | ((X1) = (k1_xboole_0))
% 0.19/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.52  thf('27', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.52         ((k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11)
% 0.19/0.52           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X8 @ X9 @ X10) @ X11))),
% 0.19/0.52      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i]:
% 0.19/0.52         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['28', '30'])).
% 0.19/0.52  thf('32', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_B) = (k1_xboole_0))
% 0.19/0.52          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['27', '31'])).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.19/0.52         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.52         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.19/0.52          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.19/0.52          | ((X0) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.52  thf('36', plain,
% 0.19/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.52  thf('37', plain,
% 0.19/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.19/0.52          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.19/0.52          | ((X0) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.52  thf('39', plain,
% 0.19/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.52  thf('40', plain,
% 0.19/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.19/0.52  thf('41', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X0) = (k1_xboole_0))
% 0.19/0.52          | ((X1) = (k1_xboole_0))
% 0.19/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.52  thf('42', plain,
% 0.19/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0))
% 0.19/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.52  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('45', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('46', plain,
% 0.19/0.52      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A))
% 0.19/0.52        | ((sk_B) = (sk_A))
% 0.19/0.52        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['4', '43', '44', '45'])).
% 0.19/0.52  thf('47', plain, (((sk_A) != (sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('48', plain,
% 0.19/0.52      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A))
% 0.19/0.52        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A)))),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.19/0.52  thf('49', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['28', '30'])).
% 0.19/0.52  thf('50', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('52', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A) = (sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.19/0.52  thf('53', plain,
% 0.19/0.52      ((((sk_A) != (sk_A)) | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['48', '52'])).
% 0.19/0.52  thf('54', plain, (((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A))),
% 0.19/0.52      inference('simplify', [status(thm)], ['53'])).
% 0.19/0.52  thf('55', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.19/0.52          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.19/0.52          | ((X0) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.52  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('58', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('59', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (sk_A))
% 0.19/0.52          | ((k2_zfmisc_1 @ X2 @ X1) = (sk_A))
% 0.19/0.52          | ((X0) = (sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.19/0.52  thf('60', plain,
% 0.19/0.52      ((((sk_A) != (sk_A))
% 0.19/0.52        | ((sk_B) = (sk_A))
% 0.19/0.52        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['54', '59'])).
% 0.19/0.52  thf('61', plain,
% 0.19/0.52      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['60'])).
% 0.19/0.52  thf('62', plain, (((sk_A) != (sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('63', plain, (((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A))),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.19/0.52  thf('64', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X0) = (k1_xboole_0))
% 0.19/0.52          | ((X1) = (k1_xboole_0))
% 0.19/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.52  thf('65', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.52  thf('68', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((X0) = (sk_A))
% 0.19/0.52          | ((X1) = (sk_A))
% 0.19/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.19/0.52  thf('69', plain,
% 0.19/0.52      ((((sk_A) != (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['63', '68'])).
% 0.19/0.52  thf('70', plain, (((sk_B) = (sk_A))),
% 0.19/0.52      inference('simplify', [status(thm)], ['69'])).
% 0.19/0.52  thf('71', plain, (((sk_A) != (sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('72', plain, ($false),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
