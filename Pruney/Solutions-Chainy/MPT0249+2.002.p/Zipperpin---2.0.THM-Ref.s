%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KXpJtwJ8mJ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 299 expanded)
%              Number of leaves         :   21 (  97 expanded)
%              Depth                    :   21
%              Number of atoms          :  486 (2279 expanded)
%              Number of equality atoms :   57 ( 367 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('7',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X45: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X45 ) @ X47 )
      | ~ ( r2_hidden @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('21',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','21'])).

thf('23',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','22'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X0 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( ( k2_xboole_0 @ sk_C_2 @ sk_B_1 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('35',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','22'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( sk_B_1 = sk_C_2 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('40',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','22'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_C_2 @ sk_B_1 ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','21'])).

thf('51',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_hidden @ sk_A @ sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['38','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KXpJtwJ8mJ
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 104 iterations in 0.042s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.48  thf(t44_zfmisc_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.48          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.48             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.19/0.48  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t7_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.48  thf('3', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf(d10_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X5 : $i, X7 : $i]:
% 0.19/0.48         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.19/0.48        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(t7_xboole_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.48  thf('7', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf(d3_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.48          | (r2_hidden @ X0 @ X2)
% 0.19/0.48          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))
% 0.19/0.48        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '9'])).
% 0.19/0.48  thf('11', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('12', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf(d1_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X15 @ X14)
% 0.19/0.48          | ((X15) = (X12))
% 0.19/0.48          | ((X14) != (k1_tarski @ X12)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X12 : $i, X15 : $i]:
% 0.19/0.48         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.48  thf('15', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (((r2_hidden @ sk_A @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('19', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf(l1_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X45 : $i, X47 : $i]:
% 0.19/0.48         ((r1_tarski @ (k1_tarski @ X45) @ X47) | ~ (r2_hidden @ X45 @ X47))),
% 0.19/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.48  thf('21', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.19/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.49  thf('22', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['5', '21'])).
% 0.19/0.49  thf('23', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.19/0.49      inference('demod', [status(thm)], ['0', '22'])).
% 0.19/0.49  thf(commutativity_k2_tarski, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.49  thf(l51_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X48 : $i, X49 : $i]:
% 0.19/0.49         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 0.19/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X48 : $i, X49 : $i]:
% 0.19/0.49         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 0.19/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X5 : $i, X7 : $i]:
% 0.19/0.49         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.19/0.49          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.19/0.49          | ((k2_xboole_0 @ X0 @ X1) = (X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['28', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_B_1 @ sk_C_2)
% 0.19/0.49        | ((k2_xboole_0 @ sk_C_2 @ sk_B_1) = (sk_C_2)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('35', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.19/0.49      inference('demod', [status(thm)], ['0', '22'])).
% 0.19/0.49  thf('36', plain, ((~ (r1_tarski @ sk_B_1 @ sk_C_2) | ((sk_B_1) = (sk_C_2)))),
% 0.19/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.19/0.49  thf('37', plain, (((sk_B_1) != (sk_C_2))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('38', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.49  thf('40', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.19/0.49      inference('demod', [status(thm)], ['0', '22'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('44', plain, ((r1_tarski @ sk_C_2 @ sk_B_1)),
% 0.19/0.49      inference('sup+', [status(thm)], ['40', '43'])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.49          | (r2_hidden @ X0 @ X2)
% 0.19/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.19/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['39', '46'])).
% 0.19/0.49  thf('48', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('49', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.19/0.49  thf('50', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['5', '21'])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      (![X12 : $i, X15 : $i]:
% 0.19/0.49         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.49  thf('53', plain, (((sk_B @ sk_C_2) = (sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['49', '52'])).
% 0.19/0.49  thf('54', plain,
% 0.19/0.49      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ sk_C_2) | ((sk_C_2) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['53', '54'])).
% 0.19/0.49  thf('56', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('57', plain, ((r2_hidden @ sk_A @ sk_C_2)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.19/0.49  thf('58', plain,
% 0.19/0.49      (![X1 : $i, X3 : $i]:
% 0.19/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.49  thf('59', plain,
% 0.19/0.49      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.49  thf('60', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.49  thf('61', plain,
% 0.19/0.49      (![X1 : $i, X3 : $i]:
% 0.19/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.49  thf('62', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r2_hidden @ sk_A @ X0)
% 0.19/0.49          | (r1_tarski @ sk_B_1 @ X0)
% 0.19/0.49          | (r1_tarski @ sk_B_1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.49  thf('63', plain,
% 0.19/0.49      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.19/0.49      inference('simplify', [status(thm)], ['62'])).
% 0.19/0.49  thf('64', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.19/0.49      inference('sup-', [status(thm)], ['57', '63'])).
% 0.19/0.49  thf('65', plain, ($false), inference('demod', [status(thm)], ['38', '64'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
