%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U4VYoRfPHc

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:02 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  235 ( 281 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
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

thf('4',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('7',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k10_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( sk_D @ X16 @ X14 @ X15 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ k1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_C @ k1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_C @ k1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U4VYoRfPHc
% 0.17/0.38  % Computer   : n010.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 20:50:30 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.25/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.52  % Solved by: fo/fo7.sh
% 0.25/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.52  % done 44 iterations in 0.031s
% 0.25/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.52  % SZS output start Refutation
% 0.25/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.25/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.25/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.25/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.25/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.52  thf(t172_relat_1, conjecture,
% 0.25/0.52    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.25/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.52    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.25/0.52    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.25/0.52  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(t60_relat_1, axiom,
% 0.25/0.52    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.25/0.52     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.25/0.52  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.25/0.52  thf(t2_tarski, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.25/0.52       ( ( A ) = ( B ) ) ))).
% 0.25/0.52  thf('2', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i]:
% 0.25/0.52         (((X1) = (X0))
% 0.25/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.25/0.52          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.25/0.52      inference('cnf', [status(esa)], [t2_tarski])).
% 0.25/0.52  thf(t2_boole, axiom,
% 0.25/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.25/0.52  thf('3', plain,
% 0.25/0.52      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.25/0.52  thf(t4_xboole_0, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.25/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.25/0.52  thf('4', plain,
% 0.25/0.52      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.25/0.52          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.25/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.25/0.52  thf('5', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.25/0.52  thf('6', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.25/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.25/0.52  thf('7', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.25/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.25/0.52  thf('8', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['2', '7'])).
% 0.25/0.52  thf(t166_relat_1, axiom,
% 0.25/0.52    (![A:$i,B:$i,C:$i]:
% 0.25/0.52     ( ( v1_relat_1 @ C ) =>
% 0.25/0.52       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.25/0.52         ( ?[D:$i]:
% 0.25/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.25/0.52             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.25/0.52             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.25/0.52  thf('9', plain,
% 0.25/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X15 @ (k10_relat_1 @ X16 @ X14))
% 0.25/0.52          | (r2_hidden @ (sk_D @ X16 @ X14 @ X15) @ (k2_relat_1 @ X16))
% 0.25/0.52          | ~ (v1_relat_1 @ X16))),
% 0.25/0.52      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.25/0.52  thf('10', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i]:
% 0.25/0.52         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.25/0.52          | ~ (v1_relat_1 @ X1)
% 0.25/0.52          | (r2_hidden @ 
% 0.25/0.52             (sk_D @ X1 @ X0 @ (sk_C @ k1_xboole_0 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.25/0.52             (k2_relat_1 @ X1)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.25/0.52  thf('11', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((r2_hidden @ 
% 0.25/0.52           (sk_D @ k1_xboole_0 @ X0 @ 
% 0.25/0.52            (sk_C @ k1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.25/0.52           k1_xboole_0)
% 0.25/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.25/0.52          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.25/0.52      inference('sup+', [status(thm)], ['1', '10'])).
% 0.25/0.52  thf(t113_zfmisc_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.25/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.25/0.52  thf('12', plain,
% 0.25/0.52      (![X9 : $i, X10 : $i]:
% 0.25/0.52         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.25/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.25/0.52  thf('13', plain,
% 0.25/0.52      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.25/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.25/0.52  thf(fc6_relat_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.25/0.52  thf('14', plain,
% 0.25/0.52      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.25/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.25/0.52  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.25/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.25/0.52  thf('16', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((r2_hidden @ 
% 0.25/0.52           (sk_D @ k1_xboole_0 @ X0 @ 
% 0.25/0.52            (sk_C @ k1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.25/0.52           k1_xboole_0)
% 0.25/0.52          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.25/0.52      inference('demod', [status(thm)], ['11', '15'])).
% 0.25/0.52  thf('17', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.25/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.25/0.52  thf('18', plain,
% 0.25/0.52      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.25/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.25/0.52  thf('19', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.25/0.52      inference('demod', [status(thm)], ['0', '18'])).
% 0.25/0.52  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.25/0.52  
% 0.25/0.52  % SZS output end Refutation
% 0.25/0.52  
% 0.25/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
