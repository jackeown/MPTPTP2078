%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ehFufJReZN

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  75 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  279 ( 414 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t5_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ A )
     => ( ( k1_setfam_1 @ A )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k1_setfam_1 @ A )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t5_setfam_1])).

thf('4',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) )
      | ( r2_hidden @ ( sk_F @ X13 @ X12 @ X11 ) @ X12 )
      | ~ ( r2_hidden @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_F @ ( sk_B @ ( k1_setfam_1 @ sk_A ) ) @ X0 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ( k1_setfam_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ ( k1_setfam_1 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('21',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('22',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ ( sk_B @ ( k1_setfam_1 @ sk_A ) ) @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_F @ ( sk_B @ ( k1_setfam_1 @ sk_A ) ) @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','22'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_F @ ( sk_B @ ( k1_setfam_1 @ sk_A ) ) @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('30',plain,(
    $false ),
    inference('sup-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ehFufJReZN
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 101 iterations in 0.068s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(t113_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.20/0.52          | ((X16) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.52  thf(d1_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf(l13_xboole_0, axiom,
% 0.20/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.52  thf(t5_setfam_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.52       ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.52          ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t5_setfam_1])).
% 0.20/0.52  thf('4', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(t4_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_setfam_1 @ X17) @ X18) | ~ (r2_hidden @ X18 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X0) | (r1_tarski @ (k1_setfam_1 @ sk_A) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(t103_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.52          ( r2_hidden @ D @ A ) & 
% 0.20/0.52          ( ![E:$i,F:$i]:
% 0.20/0.52            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.52                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X10 @ (k2_zfmisc_1 @ X11 @ X12))
% 0.20/0.52          | (r2_hidden @ (sk_F @ X13 @ X12 @ X11) @ X12)
% 0.20/0.52          | ~ (r2_hidden @ X13 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.52          | ~ (r2_hidden @ X2 @ (k1_setfam_1 @ sk_A))
% 0.20/0.52          | (r2_hidden @ (sk_F @ X2 @ X0 @ X1) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (k1_setfam_1 @ sk_A))
% 0.20/0.52          | (r2_hidden @ (sk_F @ (sk_B @ (k1_setfam_1 @ sk_A)) @ X0 @ X1) @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain, (((k1_setfam_1 @ sk_A) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) != (k1_xboole_0))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ (k1_setfam_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((~ (v1_xboole_0 @ (k1_setfam_1 @ sk_A)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf(t2_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.52  thf(t4_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.20/0.52          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.52  thf('21', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.20/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.52  thf('22', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '22'])).
% 0.20/0.52  thf('24', plain, (~ (v1_xboole_0 @ (k1_setfam_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.52          | (r2_hidden @ (sk_F @ (sk_B @ (k1_setfam_1 @ sk_A)) @ X0 @ X1) @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['10', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_F @ (sk_B @ (k1_setfam_1 @ sk_A)) @ k1_xboole_0 @ X0) @ 
% 0.20/0.52             k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '25'])).
% 0.20/0.52  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '22'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (r2_hidden @ 
% 0.20/0.52          (sk_F @ (sk_B @ (k1_setfam_1 @ sk_A)) @ k1_xboole_0 @ X0) @ 
% 0.20/0.52          k1_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('30', plain, ($false), inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
