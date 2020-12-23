%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L9DCKo8exJ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:16 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  339 ( 417 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t143_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) )
                = k1_xboole_0 ) )
       => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) )
                  = k1_xboole_0 ) )
         => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) )
        = X28 )
      | ( r2_hidden @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','8'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 ) @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ( ( k4_xboole_0 @ X28 @ ( k1_tarski @ X27 ) )
       != X28 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['11','15'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X32 ) @ X33 )
      | ( ( k10_relat_1 @ X32 @ X33 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_tarski @ ( sk_C @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_A )
      | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ X34 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L9DCKo8exJ
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:37:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.72/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.94  % Solved by: fo/fo7.sh
% 0.72/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.94  % done 1216 iterations in 0.484s
% 0.72/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.94  % SZS output start Refutation
% 0.72/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.72/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.94  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.72/0.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.72/0.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.72/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.72/0.94  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.72/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.72/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.72/0.94  thf(t143_funct_1, conjecture,
% 0.72/0.94    (![A:$i,B:$i]:
% 0.72/0.94     ( ( v1_relat_1 @ B ) =>
% 0.72/0.94       ( ( ![C:$i]:
% 0.72/0.94           ( ~( ( r2_hidden @ C @ A ) & 
% 0.72/0.94                ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.72/0.94         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.72/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.94    (~( ![A:$i,B:$i]:
% 0.72/0.94        ( ( v1_relat_1 @ B ) =>
% 0.72/0.94          ( ( ![C:$i]:
% 0.72/0.94              ( ~( ( r2_hidden @ C @ A ) & 
% 0.72/0.94                   ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.72/0.94            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )),
% 0.72/0.94    inference('cnf.neg', [status(esa)], [t143_funct_1])).
% 0.72/0.94  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.72/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.94  thf(d3_tarski, axiom,
% 0.72/0.94    (![A:$i,B:$i]:
% 0.72/0.94     ( ( r1_tarski @ A @ B ) <=>
% 0.72/0.94       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.72/0.94  thf('1', plain,
% 0.72/0.94      (![X1 : $i, X3 : $i]:
% 0.72/0.94         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.72/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.94  thf(t65_zfmisc_1, axiom,
% 0.72/0.94    (![A:$i,B:$i]:
% 0.72/0.94     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.72/0.94       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.72/0.94  thf('2', plain,
% 0.72/0.94      (![X28 : $i, X29 : $i]:
% 0.72/0.94         (((k4_xboole_0 @ X28 @ (k1_tarski @ X29)) = (X28))
% 0.72/0.94          | (r2_hidden @ X29 @ X28))),
% 0.72/0.94      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.72/0.94  thf(t48_xboole_1, axiom,
% 0.72/0.94    (![A:$i,B:$i]:
% 0.72/0.94     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.72/0.94  thf('3', plain,
% 0.72/0.94      (![X14 : $i, X15 : $i]:
% 0.72/0.94         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.72/0.94           = (k3_xboole_0 @ X14 @ X15))),
% 0.72/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.94  thf('4', plain,
% 0.72/0.94      (![X0 : $i, X1 : $i]:
% 0.72/0.94         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.72/0.94          | (r2_hidden @ X1 @ X0))),
% 0.72/0.94      inference('sup+', [status(thm)], ['2', '3'])).
% 0.72/0.94  thf(d10_xboole_0, axiom,
% 0.72/0.94    (![A:$i,B:$i]:
% 0.72/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.72/0.94  thf('5', plain,
% 0.72/0.94      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.72/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.72/0.94  thf('6', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.72/0.94      inference('simplify', [status(thm)], ['5'])).
% 0.72/0.94  thf(l32_xboole_1, axiom,
% 0.72/0.94    (![A:$i,B:$i]:
% 0.72/0.94     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.72/0.94  thf('7', plain,
% 0.72/0.94      (![X11 : $i, X13 : $i]:
% 0.72/0.94         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.72/0.94          | ~ (r1_tarski @ X11 @ X13))),
% 0.72/0.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.72/0.94  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.72/0.94      inference('sup-', [status(thm)], ['6', '7'])).
% 0.72/0.94  thf('9', plain,
% 0.72/0.94      (![X0 : $i, X1 : $i]:
% 0.72/0.94         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.72/0.94          | (r2_hidden @ X1 @ X0))),
% 0.72/0.94      inference('demod', [status(thm)], ['4', '8'])).
% 0.72/0.94  thf(t4_xboole_0, axiom,
% 0.72/0.94    (![A:$i,B:$i]:
% 0.72/0.94     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.94            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.94       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.72/0.94            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.72/0.94  thf('10', plain,
% 0.72/0.94      (![X4 : $i, X5 : $i]:
% 0.72/0.94         ((r1_xboole_0 @ X4 @ X5)
% 0.72/0.94          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.72/0.94      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.72/0.94  thf('11', plain,
% 0.72/0.94      (![X0 : $i, X1 : $i]:
% 0.72/0.94         ((r2_hidden @ (sk_C_1 @ (k1_tarski @ X0) @ X1) @ k1_xboole_0)
% 0.72/0.94          | (r2_hidden @ X0 @ X1)
% 0.72/0.94          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.72/0.94      inference('sup+', [status(thm)], ['9', '10'])).
% 0.72/0.94  thf(t4_boole, axiom,
% 0.72/0.94    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.72/0.94  thf('12', plain,
% 0.72/0.94      (![X16 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.72/0.94      inference('cnf', [status(esa)], [t4_boole])).
% 0.72/0.94  thf('13', plain,
% 0.72/0.94      (![X27 : $i, X28 : $i]:
% 0.72/0.94         (~ (r2_hidden @ X27 @ X28)
% 0.72/0.94          | ((k4_xboole_0 @ X28 @ (k1_tarski @ X27)) != (X28)))),
% 0.72/0.94      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.72/0.94  thf('14', plain,
% 0.72/0.94      (![X0 : $i]:
% 0.72/0.94         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.72/0.94      inference('sup-', [status(thm)], ['12', '13'])).
% 0.72/0.94  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.72/0.94      inference('simplify', [status(thm)], ['14'])).
% 0.72/0.94  thf('16', plain,
% 0.72/0.94      (![X0 : $i, X1 : $i]:
% 0.72/0.94         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.72/0.94      inference('clc', [status(thm)], ['11', '15'])).
% 0.72/0.94  thf(t173_relat_1, axiom,
% 0.72/0.94    (![A:$i,B:$i]:
% 0.72/0.94     ( ( v1_relat_1 @ B ) =>
% 0.72/0.94       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.72/0.94         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.72/0.94  thf('17', plain,
% 0.72/0.94      (![X32 : $i, X33 : $i]:
% 0.72/0.94         (~ (r1_xboole_0 @ (k2_relat_1 @ X32) @ X33)
% 0.72/0.94          | ((k10_relat_1 @ X32 @ X33) = (k1_xboole_0))
% 0.72/0.94          | ~ (v1_relat_1 @ X32))),
% 0.72/0.94      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.72/0.94  thf('18', plain,
% 0.72/0.94      (![X0 : $i, X1 : $i]:
% 0.72/0.94         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.72/0.94          | ~ (v1_relat_1 @ X1)
% 0.72/0.94          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.72/0.94      inference('sup-', [status(thm)], ['16', '17'])).
% 0.72/0.94  thf('19', plain,
% 0.72/0.94      (![X1 : $i, X3 : $i]:
% 0.72/0.94         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.72/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.94  thf('20', plain,
% 0.72/0.94      (![X0 : $i, X1 : $i]:
% 0.72/0.94         (((k10_relat_1 @ X0 @ (k1_tarski @ (sk_C @ (k2_relat_1 @ X0) @ X1)))
% 0.72/0.94            = (k1_xboole_0))
% 0.72/0.94          | ~ (v1_relat_1 @ X0)
% 0.72/0.94          | (r1_tarski @ X1 @ (k2_relat_1 @ X0)))),
% 0.72/0.94      inference('sup-', [status(thm)], ['18', '19'])).
% 0.72/0.94  thf('21', plain,
% 0.72/0.94      (![X34 : $i]:
% 0.72/0.94         (~ (r2_hidden @ X34 @ sk_A)
% 0.72/0.94          | ((k10_relat_1 @ sk_B @ (k1_tarski @ X34)) != (k1_xboole_0)))),
% 0.72/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.94  thf('22', plain,
% 0.72/0.94      (![X0 : $i]:
% 0.72/0.94         (((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.94          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_B))
% 0.72/0.94          | ~ (v1_relat_1 @ sk_B)
% 0.72/0.94          | ~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ X0) @ sk_A))),
% 0.72/0.94      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.94  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.72/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.94  thf('24', plain,
% 0.72/0.94      (![X0 : $i]:
% 0.72/0.94         (((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.94          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_B))
% 0.72/0.94          | ~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ X0) @ sk_A))),
% 0.72/0.94      inference('demod', [status(thm)], ['22', '23'])).
% 0.72/0.94  thf('25', plain,
% 0.72/0.94      (![X0 : $i]:
% 0.72/0.94         (~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.72/0.94          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.72/0.94      inference('simplify', [status(thm)], ['24'])).
% 0.72/0.94  thf('26', plain,
% 0.72/0.94      (((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.72/0.94        | (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.72/0.94      inference('sup-', [status(thm)], ['1', '25'])).
% 0.72/0.94  thf('27', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.72/0.94      inference('simplify', [status(thm)], ['26'])).
% 0.72/0.94  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.72/0.94  
% 0.72/0.94  % SZS output end Refutation
% 0.72/0.94  
% 0.77/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
