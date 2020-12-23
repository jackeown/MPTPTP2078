%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hXrrBD6jZf

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  138 ( 178 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X11 ) @ ( sk_D @ X10 @ X11 ) ) @ X11 )
      | ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t56_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ! [B: $i,C: $i] :
              ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_relat_1])).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hXrrBD6jZf
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 18 iterations in 0.012s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.46  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(d3_relat_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.46           ( ![C:$i,D:$i]:
% 0.20/0.46             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.20/0.46               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i]:
% 0.20/0.46         ((r2_hidden @ 
% 0.20/0.46           (k4_tarski @ (sk_C_1 @ X10 @ X11) @ (sk_D @ X10 @ X11)) @ X11)
% 0.20/0.46          | (r1_tarski @ X11 @ X10)
% 0.20/0.46          | ~ (v1_relat_1 @ X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.46  thf(t56_relat_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.20/0.46         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( v1_relat_1 @ A ) =>
% 0.20/0.46          ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.20/0.46            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t56_relat_1])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i]: (~ (v1_relat_1 @ sk_A) | (r1_tarski @ sk_A @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf('3', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('4', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(d3_tarski, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.46  thf('6', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.20/0.46      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.46  thf(l24_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         (~ (r1_xboole_0 @ (k1_tarski @ X8) @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.20/0.46  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.46  thf(d10_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X4 : $i, X6 : $i]:
% 0.20/0.46         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.46  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('14', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
