%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.upxsvjZ3K8

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 435 expanded)
%              Number of leaves         :   11 ( 128 expanded)
%              Depth                    :   22
%              Number of atoms          :  575 (4745 expanded)
%              Number of equality atoms :  131 (1027 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t38_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_zfmisc_1 @ A @ A @ A )
        = ( k3_zfmisc_1 @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_zfmisc_1 @ A @ A @ A )
          = ( k3_zfmisc_1 @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t38_mcart_1])).

thf('0',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('10',plain,
    ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A ) )
      = sk_B )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_A = sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ X1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('34',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('35',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != sk_A )
    | ( sk_B = sk_A )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['4','32','33','34'])).

thf('36',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != sk_A )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','42'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('45',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ sk_A @ X0 )
      = sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( sk_A != sk_A )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_B )
    = sk_A ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('50',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_A )
      | ( X1 = sk_A )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.upxsvjZ3K8
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:44:41 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 60 iterations in 0.029s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(t38_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.20/0.48       ( ( A ) = ( B ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.20/0.48          ( ( A ) = ( B ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t38_mcart_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d3_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.48       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf(t113_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.20/0.48          | ((X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf(t195_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.20/0.48               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (((X3) = (k1_xboole_0))
% 0.20/0.48          | ((k2_relat_1 @ (k2_zfmisc_1 @ X3 @ X4)) = (X4))
% 0.20/0.48          | ((X4) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.20/0.48          | ((X0) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.20/0.48          | ((X0) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((((k2_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_A @ sk_A)) = (sk_B))
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((((sk_A) = (sk_B))
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '10'])).
% 0.20/0.48  thf('12', plain, (((sk_A) != (sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((sk_B) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['20', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k3_zfmisc_1 @ X1 @ X0 @ sk_B) = (k1_xboole_0))
% 0.20/0.48          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['19', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.20/0.48          | ((X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('33', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('34', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (sk_A))
% 0.20/0.48        | ((sk_B) = (sk_A))
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '32', '33', '34'])).
% 0.20/0.48  thf('36', plain, (((sk_A) != (sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (sk_A))
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 0.20/0.48           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['40', '42'])).
% 0.20/0.48  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('45', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_zfmisc_1 @ X1 @ sk_A @ X0) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((((sk_A) != (sk_A)) | ((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['37', '46'])).
% 0.20/0.48  thf('48', plain, (((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('50', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) = (sk_A))
% 0.20/0.48          | ((X1) = (sk_A))
% 0.20/0.48          | ((k2_zfmisc_1 @ X1 @ X0) != (sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      ((((sk_A) != (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['48', '53'])).
% 0.20/0.48  thf('55', plain, (((sk_B) = (sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.48  thf('56', plain, (((sk_A) != (sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('57', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.35/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
