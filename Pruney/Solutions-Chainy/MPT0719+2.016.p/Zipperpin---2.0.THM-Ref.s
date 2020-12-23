%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2zDRM2MG0F

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:27 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   50 (  55 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 ( 285 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X16 ) @ ( k1_relat_1 @ X15 ) )
      | ( v5_funct_1 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_C @ X12 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('12',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('16',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2zDRM2MG0F
% 0.16/0.38  % Computer   : n019.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 20:22:22 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 38 iterations in 0.023s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i > $i).
% 0.24/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.51  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.24/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.24/0.51  thf(cc1_funct_1, axiom,
% 0.24/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.24/0.51  thf('0', plain, (![X14 : $i]: ((v1_funct_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.24/0.51      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.24/0.51  thf(cc1_relat_1, axiom,
% 0.24/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.24/0.51  thf('1', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.24/0.51      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.24/0.51  thf(fc11_relat_1, axiom,
% 0.24/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X11 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ (k2_relat_1 @ X11)) | ~ (v1_xboole_0 @ X11))),
% 0.24/0.51      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.24/0.51  thf(l13_xboole_0, axiom,
% 0.24/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.51  thf(d20_funct_1, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.51       ( ![B:$i]:
% 0.24/0.51         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.51           ( ( v5_funct_1 @ B @ A ) <=>
% 0.24/0.51             ( ![C:$i]:
% 0.24/0.51               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.24/0.51                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X15 : $i, X16 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X15)
% 0.24/0.51          | ~ (v1_funct_1 @ X15)
% 0.24/0.51          | (r2_hidden @ (sk_C_1 @ X15 @ X16) @ (k1_relat_1 @ X15))
% 0.24/0.51          | (v5_funct_1 @ X15 @ X16)
% 0.24/0.51          | ~ (v1_funct_1 @ X16)
% 0.24/0.51          | ~ (v1_relat_1 @ X16))),
% 0.24/0.51      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.24/0.51  thf(t18_relat_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ B ) =>
% 0.24/0.51       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.24/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X12 : $i, X13 : $i]:
% 0.24/0.51         ((r2_hidden @ (sk_C @ X12) @ (k2_relat_1 @ X12))
% 0.24/0.51          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.24/0.51          | ~ (v1_relat_1 @ X12))),
% 0.24/0.51      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_funct_1 @ X1)
% 0.24/0.51          | (v5_funct_1 @ X0 @ X1)
% 0.24/0.51          | ~ (v1_funct_1 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X0)
% 0.24/0.51          | (r2_hidden @ (sk_C @ X0) @ (k2_relat_1 @ X0)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((r2_hidden @ (sk_C @ X0) @ (k2_relat_1 @ X0))
% 0.24/0.51          | ~ (v1_relat_1 @ X0)
% 0.24/0.51          | ~ (v1_funct_1 @ X0)
% 0.24/0.51          | (v5_funct_1 @ X0 @ X1)
% 0.24/0.51          | ~ (v1_funct_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X1))),
% 0.24/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((r2_hidden @ (sk_C @ X0) @ k1_xboole_0)
% 0.24/0.51          | ~ (v1_xboole_0 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_funct_1 @ X1)
% 0.24/0.51          | (v5_funct_1 @ X0 @ X1)
% 0.24/0.51          | ~ (v1_funct_1 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X0))),
% 0.24/0.51      inference('sup+', [status(thm)], ['4', '8'])).
% 0.24/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.24/0.51  thf('10', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.24/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.24/0.51  thf(t55_zfmisc_1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.51         (~ (r1_xboole_0 @ (k2_tarski @ X7 @ X8) @ X9)
% 0.24/0.51          | ~ (r2_hidden @ X7 @ X9))),
% 0.24/0.51      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.24/0.51  thf('12', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.24/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X0)
% 0.24/0.51          | ~ (v1_funct_1 @ X0)
% 0.24/0.51          | (v5_funct_1 @ X0 @ X1)
% 0.24/0.51          | ~ (v1_funct_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_xboole_0 @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (v1_xboole_0 @ X0)
% 0.24/0.51          | ~ (v1_xboole_0 @ X0)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_funct_1 @ X1)
% 0.24/0.51          | (v5_funct_1 @ X0 @ X1)
% 0.24/0.51          | ~ (v1_funct_1 @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['1', '13'])).
% 0.24/0.51  thf('15', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (~ (v1_funct_1 @ X0)
% 0.24/0.51          | (v5_funct_1 @ X0 @ X1)
% 0.24/0.51          | ~ (v1_funct_1 @ X1)
% 0.24/0.51          | ~ (v1_relat_1 @ X1)
% 0.24/0.51          | ~ (v1_xboole_0 @ X0))),
% 0.24/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.24/0.51  thf(t174_funct_1, conjecture,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.51       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i]:
% 0.24/0.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.51          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.24/0.51  thf('16', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('17', plain,
% 0.24/0.51      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.51        | ~ (v1_relat_1 @ sk_A)
% 0.24/0.51        | ~ (v1_funct_1 @ sk_A)
% 0.24/0.51        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.51  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.51  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('20', plain, ((v1_funct_1 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('21', plain, (~ (v1_funct_1 @ k1_xboole_0)),
% 0.24/0.51      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.24/0.51  thf('22', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.51      inference('sup-', [status(thm)], ['0', '21'])).
% 0.24/0.51  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.51  thf('24', plain, ($false), inference('demod', [status(thm)], ['22', '23'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
