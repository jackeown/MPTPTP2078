%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OgK4WgXv96

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:11 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  89 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  371 ( 657 expanded)
%              Number of equality atoms :   17 (  53 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t174_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( ( k10_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t174_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['5','9'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X16 @ X14 @ X15 ) @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( sk_B @ sk_A ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X18 ) @ X21 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X21 ) )
      | ( r2_hidden @ X20 @ ( k10_relat_1 @ X21 @ X19 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k10_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['5','9'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k10_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k10_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','22'])).

thf('24',plain,
    ( ( k10_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['8'])).

thf('27',plain,(
    r2_hidden @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['25','26'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('29',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference('sup-',[status(thm)],['27','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OgK4WgXv96
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:38:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.20/2.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.20/2.38  % Solved by: fo/fo7.sh
% 2.20/2.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.20/2.38  % done 4320 iterations in 1.932s
% 2.20/2.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.20/2.38  % SZS output start Refutation
% 2.20/2.38  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.20/2.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.20/2.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.20/2.38  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.20/2.38  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.20/2.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.20/2.38  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.20/2.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.20/2.38  thf(sk_B_type, type, sk_B: $i > $i).
% 2.20/2.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.20/2.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.20/2.38  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.20/2.38  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.20/2.38  thf(sk_A_type, type, sk_A: $i).
% 2.20/2.38  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.20/2.38  thf(d1_xboole_0, axiom,
% 2.20/2.38    (![A:$i]:
% 2.20/2.38     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.20/2.38  thf('0', plain,
% 2.20/2.38      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.20/2.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.20/2.38  thf('1', plain,
% 2.20/2.38      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.20/2.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.20/2.38  thf(t174_relat_1, conjecture,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( v1_relat_1 @ B ) =>
% 2.20/2.38       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.20/2.38            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 2.20/2.38            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 2.20/2.38  thf(zf_stmt_0, negated_conjecture,
% 2.20/2.38    (~( ![A:$i,B:$i]:
% 2.20/2.38        ( ( v1_relat_1 @ B ) =>
% 2.20/2.38          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.20/2.38               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 2.20/2.38               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 2.20/2.38    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 2.20/2.38  thf('2', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B_1))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf(d3_tarski, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( r1_tarski @ A @ B ) <=>
% 2.20/2.38       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.20/2.38  thf('3', plain,
% 2.20/2.38      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.20/2.38         (~ (r2_hidden @ X3 @ X4)
% 2.20/2.38          | (r2_hidden @ X3 @ X5)
% 2.20/2.38          | ~ (r1_tarski @ X4 @ X5))),
% 2.20/2.38      inference('cnf', [status(esa)], [d3_tarski])).
% 2.20/2.38  thf('4', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1)) | ~ (r2_hidden @ X0 @ sk_A))),
% 2.20/2.38      inference('sup-', [status(thm)], ['2', '3'])).
% 2.20/2.38  thf('5', plain,
% 2.20/2.38      (((v1_xboole_0 @ sk_A)
% 2.20/2.38        | (r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1)))),
% 2.20/2.38      inference('sup-', [status(thm)], ['1', '4'])).
% 2.20/2.38  thf(l13_xboole_0, axiom,
% 2.20/2.38    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.20/2.38  thf('6', plain,
% 2.20/2.38      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 2.20/2.38      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.20/2.38  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('8', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['6', '7'])).
% 2.20/2.38  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.20/2.38      inference('simplify', [status(thm)], ['8'])).
% 2.20/2.38  thf('10', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 2.20/2.38      inference('clc', [status(thm)], ['5', '9'])).
% 2.20/2.38  thf(t146_relat_1, axiom,
% 2.20/2.38    (![A:$i]:
% 2.20/2.38     ( ( v1_relat_1 @ A ) =>
% 2.20/2.38       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.20/2.38  thf('11', plain,
% 2.20/2.38      (![X17 : $i]:
% 2.20/2.38         (((k9_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (k2_relat_1 @ X17))
% 2.20/2.38          | ~ (v1_relat_1 @ X17))),
% 2.20/2.38      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.20/2.38  thf(t143_relat_1, axiom,
% 2.20/2.38    (![A:$i,B:$i,C:$i]:
% 2.20/2.38     ( ( v1_relat_1 @ C ) =>
% 2.20/2.38       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 2.20/2.38         ( ?[D:$i]:
% 2.20/2.38           ( ( r2_hidden @ D @ B ) & 
% 2.20/2.38             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 2.20/2.38             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 2.20/2.38  thf('12', plain,
% 2.20/2.38      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.20/2.38         (~ (r2_hidden @ X15 @ (k9_relat_1 @ X16 @ X14))
% 2.20/2.38          | (r2_hidden @ (k4_tarski @ (sk_D @ X16 @ X14 @ X15) @ X15) @ X16)
% 2.20/2.38          | ~ (v1_relat_1 @ X16))),
% 2.20/2.38      inference('cnf', [status(esa)], [t143_relat_1])).
% 2.20/2.38  thf('13', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 2.20/2.38          | ~ (v1_relat_1 @ X0)
% 2.20/2.38          | ~ (v1_relat_1 @ X0)
% 2.20/2.38          | (r2_hidden @ 
% 2.20/2.38             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['11', '12'])).
% 2.20/2.38  thf('14', plain,
% 2.20/2.38      (![X0 : $i, X1 : $i]:
% 2.20/2.38         ((r2_hidden @ 
% 2.20/2.38           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 2.20/2.38          | ~ (v1_relat_1 @ X0)
% 2.20/2.38          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 2.20/2.38      inference('simplify', [status(thm)], ['13'])).
% 2.20/2.38  thf('15', plain,
% 2.20/2.38      ((~ (v1_relat_1 @ sk_B_1)
% 2.20/2.38        | (r2_hidden @ 
% 2.20/2.38           (k4_tarski @ 
% 2.20/2.38            (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 2.20/2.38            (sk_B @ sk_A)) @ 
% 2.20/2.38           sk_B_1))),
% 2.20/2.38      inference('sup-', [status(thm)], ['10', '14'])).
% 2.20/2.38  thf('16', plain, ((v1_relat_1 @ sk_B_1)),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('17', plain,
% 2.20/2.38      ((r2_hidden @ 
% 2.20/2.38        (k4_tarski @ (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 2.20/2.38         (sk_B @ sk_A)) @ 
% 2.20/2.38        sk_B_1)),
% 2.20/2.38      inference('demod', [status(thm)], ['15', '16'])).
% 2.20/2.38  thf(t166_relat_1, axiom,
% 2.20/2.38    (![A:$i,B:$i,C:$i]:
% 2.20/2.38     ( ( v1_relat_1 @ C ) =>
% 2.20/2.38       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 2.20/2.38         ( ?[D:$i]:
% 2.20/2.38           ( ( r2_hidden @ D @ B ) & 
% 2.20/2.38             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 2.20/2.38             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 2.20/2.38  thf('18', plain,
% 2.20/2.38      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.20/2.38         (~ (r2_hidden @ X18 @ X19)
% 2.20/2.38          | ~ (r2_hidden @ (k4_tarski @ X20 @ X18) @ X21)
% 2.20/2.38          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X21))
% 2.20/2.38          | (r2_hidden @ X20 @ (k10_relat_1 @ X21 @ X19))
% 2.20/2.38          | ~ (v1_relat_1 @ X21))),
% 2.20/2.38      inference('cnf', [status(esa)], [t166_relat_1])).
% 2.20/2.38  thf('19', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         (~ (v1_relat_1 @ sk_B_1)
% 2.20/2.38          | (r2_hidden @ 
% 2.20/2.38             (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 2.20/2.38             (k10_relat_1 @ sk_B_1 @ X0))
% 2.20/2.38          | ~ (r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 2.20/2.38          | ~ (r2_hidden @ (sk_B @ sk_A) @ X0))),
% 2.20/2.38      inference('sup-', [status(thm)], ['17', '18'])).
% 2.20/2.38  thf('20', plain, ((v1_relat_1 @ sk_B_1)),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('21', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 2.20/2.38      inference('clc', [status(thm)], ['5', '9'])).
% 2.20/2.38  thf('22', plain,
% 2.20/2.38      (![X0 : $i]:
% 2.20/2.38         ((r2_hidden @ 
% 2.20/2.38           (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 2.20/2.38           (k10_relat_1 @ sk_B_1 @ X0))
% 2.20/2.38          | ~ (r2_hidden @ (sk_B @ sk_A) @ X0))),
% 2.20/2.38      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.20/2.38  thf('23', plain,
% 2.20/2.38      (((v1_xboole_0 @ sk_A)
% 2.20/2.38        | (r2_hidden @ 
% 2.20/2.38           (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 2.20/2.38           (k10_relat_1 @ sk_B_1 @ sk_A)))),
% 2.20/2.38      inference('sup-', [status(thm)], ['0', '22'])).
% 2.20/2.38  thf('24', plain, (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 2.20/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.20/2.38  thf('25', plain,
% 2.20/2.38      (((v1_xboole_0 @ sk_A)
% 2.20/2.38        | (r2_hidden @ 
% 2.20/2.38           (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 2.20/2.38           k1_xboole_0))),
% 2.20/2.38      inference('demod', [status(thm)], ['23', '24'])).
% 2.20/2.38  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.20/2.38      inference('simplify', [status(thm)], ['8'])).
% 2.20/2.38  thf('27', plain,
% 2.20/2.38      ((r2_hidden @ (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 2.20/2.38        k1_xboole_0)),
% 2.20/2.38      inference('clc', [status(thm)], ['25', '26'])).
% 2.20/2.38  thf(t113_zfmisc_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]:
% 2.20/2.38     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.20/2.38       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.20/2.38  thf('28', plain,
% 2.20/2.38      (![X9 : $i, X10 : $i]:
% 2.20/2.38         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 2.20/2.38      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.20/2.38  thf('29', plain,
% 2.20/2.38      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 2.20/2.38      inference('simplify', [status(thm)], ['28'])).
% 2.20/2.38  thf(t152_zfmisc_1, axiom,
% 2.20/2.38    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.20/2.38  thf('30', plain,
% 2.20/2.38      (![X11 : $i, X12 : $i]: ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X11 @ X12))),
% 2.20/2.38      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 2.20/2.38  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.20/2.38      inference('sup-', [status(thm)], ['29', '30'])).
% 2.20/2.38  thf('32', plain, ($false), inference('sup-', [status(thm)], ['27', '31'])).
% 2.20/2.38  
% 2.20/2.38  % SZS output end Refutation
% 2.20/2.38  
% 2.25/2.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
