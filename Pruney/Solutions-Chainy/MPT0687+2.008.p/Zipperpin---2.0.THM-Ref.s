%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HLtal3ogbl

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  97 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  346 ( 886 expanded)
%              Number of equality atoms :   36 (  88 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ ( k1_tarski @ X14 ) )
        = X13 )
      | ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k4_xboole_0 @ X4 @ X6 )
       != X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( ( k10_relat_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t142_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
        <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_1])).

thf('6',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('11',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k10_relat_1 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('13',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X13 @ ( k1_tarski @ X12 ) )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('20',plain,
    ( ( ( ( k2_relat_1 @ sk_B )
       != ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['9','22','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['7','24'])).

thf('26',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('30',plain,(
    ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','22'])).

thf('31',plain,(
    ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HLtal3ogbl
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 53 iterations in 0.028s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(t65_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.50       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ X13 @ (k1_tarski @ X14)) = (X13))
% 0.21/0.50          | (r2_hidden @ X14 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.50  thf(t83_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X4 : $i, X6 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X4 @ X6) | ((k4_xboole_0 @ X4 @ X6) != (X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((X0) != (X0))
% 0.21/0.50          | (r2_hidden @ X1 @ X0)
% 0.21/0.50          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.50  thf(t173_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.50         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ (k2_relat_1 @ X15) @ X16)
% 0.21/0.50          | ((k10_relat_1 @ X15 @ X16) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.21/0.50          | ~ (v1_relat_1 @ X1)
% 0.21/0.50          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf(t142_funct_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.21/0.50         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( v1_relat_1 @ B ) =>
% 0.21/0.50          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.21/0.50            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.21/0.50        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.21/0.50         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.21/0.50        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.21/0.50       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.21/0.50         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['8'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.21/0.50         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['6'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         (((k10_relat_1 @ X15 @ X16) != (k1_xboole_0))
% 0.21/0.50          | (r1_xboole_0 @ (k2_relat_1 @ X15) @ X16)
% 0.21/0.50          | ~ (v1_relat_1 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.50         | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.21/0.50         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50         | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.21/0.50         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.21/0.50         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((((k4_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))
% 0.21/0.50          = (k2_relat_1 @ sk_B)))
% 0.21/0.50         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X12 @ X13)
% 0.21/0.50          | ((k4_xboole_0 @ X13 @ (k1_tarski @ X12)) != (X13)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (((((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B))
% 0.21/0.50         | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.21/0.50         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.21/0.50         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 0.21/0.50       ~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 0.21/0.50       (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.21/0.50      inference('split', [status(esa)], ['6'])).
% 0.21/0.50  thf('24', plain, (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['9', '22', '23'])).
% 0.21/0.50  thf('25', plain, (~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['7', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '25'])).
% 0.21/0.50  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.21/0.50      inference('split', [status(esa)], ['8'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['9', '22'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['28', '31'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
