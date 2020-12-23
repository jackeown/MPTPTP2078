%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.asg6O86irm

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:06 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 102 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  407 ( 757 expanded)
%              Number of equality atoms :   23 (  60 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X30 ) )
      | ~ ( r2_hidden @ X28 @ X30 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['8','20'])).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X30 ) )
      | ~ ( r2_hidden @ X28 @ X30 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['28','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.asg6O86irm
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 269 iterations in 0.126s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.57  thf(d3_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i]:
% 0.37/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf(d1_xboole_0, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.57  thf(l54_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.37/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 0.37/0.57         ((r2_hidden @ (k4_tarski @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X30))
% 0.37/0.57          | ~ (r2_hidden @ X28 @ X30)
% 0.37/0.57          | ~ (r2_hidden @ X26 @ X27))),
% 0.37/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((v1_xboole_0 @ X0)
% 0.37/0.57          | ~ (r2_hidden @ X2 @ X1)
% 0.37/0.57          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.37/0.57             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r1_tarski @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 0.37/0.57             (k2_zfmisc_1 @ X0 @ X2))
% 0.37/0.57          | (v1_xboole_0 @ X2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['0', '3'])).
% 0.37/0.57  thf(t114_zfmisc_1, conjecture,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.37/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.57         ( ( A ) = ( B ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i]:
% 0.37/0.57        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.37/0.57          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.57            ( ( A ) = ( B ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.57         ((r2_hidden @ X26 @ X27)
% 0.37/0.57          | ~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X29)))),
% 0.37/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.37/0.57          | (r2_hidden @ X1 @ sk_B_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v1_xboole_0 @ sk_B_1)
% 0.37/0.57          | (r1_tarski @ sk_A @ X0)
% 0.37/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.57  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i]:
% 0.37/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf(d10_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X7 : $i, X9 : $i]:
% 0.37/0.57         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['12', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['9', '16'])).
% 0.37/0.57  thf('18', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('19', plain, (![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf('20', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1) | (r1_tarski @ sk_A @ X0))),
% 0.37/0.57      inference('clc', [status(thm)], ['8', '20'])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i]:
% 0.37/0.57         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.57  thf('24', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.37/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X7 : $i, X9 : $i]:
% 0.37/0.57         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.57  thf('26', plain, ((~ (r1_tarski @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf('27', plain, (((sk_A) != (sk_B_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('28', plain, (~ (r1_tarski @ sk_B_1 @ sk_A)),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i]:
% 0.37/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 0.37/0.57         ((r2_hidden @ (k4_tarski @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X30))
% 0.37/0.57          | ~ (r2_hidden @ X28 @ X30)
% 0.37/0.57          | ~ (r2_hidden @ X26 @ X27))),
% 0.37/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X0 @ X1)
% 0.37/0.57          | ~ (r2_hidden @ X3 @ X2)
% 0.37/0.57          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.37/0.57             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((v1_xboole_0 @ X0)
% 0.37/0.57          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 0.37/0.57             (k2_zfmisc_1 @ X0 @ X1))
% 0.37/0.57          | (r1_tarski @ X1 @ X2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['29', '32'])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.57         ((r2_hidden @ X28 @ X29)
% 0.37/0.57          | ~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X29)))),
% 0.37/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.37/0.57          | (r2_hidden @ X0 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_B_1 @ X0)
% 0.37/0.57          | (v1_xboole_0 @ sk_A)
% 0.37/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['33', '36'])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['9', '16'])).
% 0.37/0.57  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('40', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.57  thf('41', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.57      inference('simplify', [status(thm)], ['40'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A) | (r1_tarski @ sk_B_1 @ X0))),
% 0.37/0.57      inference('clc', [status(thm)], ['37', '41'])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      (![X4 : $i, X6 : $i]:
% 0.37/0.57         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (((r1_tarski @ sk_B_1 @ sk_A) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.57  thf('45', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.37/0.57      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.57  thf('46', plain, ($false), inference('demod', [status(thm)], ['28', '45'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
