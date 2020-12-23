%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fdwufjl9bj

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  439 (1099 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(t42_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C )
                & ( D != B ) ) ) )
       => ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( ( v2_wellord1 @ C )
            & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) )
            & ! [D: $i] :
                ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) )
               => ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C )
                  & ( D != B ) ) ) )
         => ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_wellord1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v6_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
              & ( B != C )
              & ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v6_relat_2 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X11 ) @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X10 )
      | ( X11 = X12 )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_1 )
      | ~ ( v6_relat_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ( v6_relat_2 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('8',plain,
    ( ( v6_relat_2 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v6_relat_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_A ) @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ( X6
       != ( k1_wellord1 @ X5 @ X4 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X4 ) @ X5 )
      | ( X8 = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('16',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( X8 = X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X4 ) @ X5 )
      | ( r2_hidden @ X8 @ ( k1_wellord1 @ X5 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( sk_B_1 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( sk_B_1 = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( sk_A = sk_B_1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X16: $i] :
      ( ( X16 != sk_B_1 )
      | ~ ( r2_hidden @ X16 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_A = sk_B_1 ),
    inference(clc,[status(thm)],['20','22'])).

thf('24',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t37_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v2_wellord1 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k3_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ X15 @ ( k3_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X13 @ X14 ) @ ( k1_wellord1 @ X13 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ X1 ) )
      | ~ ( v2_wellord1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_1 ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fdwufjl9bj
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:18:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 59 iterations in 0.075s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.53  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.53  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.20/0.53  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.20/0.53  thf(t42_wellord1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.53           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.53           ( ![D:$i]:
% 0.20/0.53             ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) ) =>
% 0.20/0.53               ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C ) & ( ( D ) != ( B ) ) ) ) ) ) =>
% 0.20/0.53         ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( v1_relat_1 @ C ) =>
% 0.20/0.53          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.53              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.53              ( ![D:$i]:
% 0.20/0.53                ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) ) =>
% 0.20/0.53                  ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C ) & 
% 0.20/0.53                    ( ( D ) != ( B ) ) ) ) ) ) =>
% 0.20/0.53            ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t42_wellord1])).
% 0.20/0.53  thf('0', plain, (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('2', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(l4_wellord1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ( v6_relat_2 @ A ) <=>
% 0.20/0.53         ( ![B:$i,C:$i]:
% 0.20/0.53           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.53                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 0.20/0.53                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 0.20/0.53                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.53         (~ (v6_relat_2 @ X10)
% 0.20/0.53          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X10))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X12 @ X11) @ X10)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X11 @ X12) @ X10)
% 0.20/0.53          | ((X11) = (X12))
% 0.20/0.53          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X10))
% 0.20/0.53          | ~ (v1_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ sk_C_1)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.20/0.53          | ((sk_A) = (X0))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_1)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_1)
% 0.20/0.53          | ~ (v6_relat_2 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d4_wellord1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ( v2_wellord1 @ A ) <=>
% 0.20/0.53         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.20/0.53           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X9 : $i]:
% 0.20/0.53         (~ (v2_wellord1 @ X9) | (v6_relat_2 @ X9) | ~ (v1_relat_1 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.20/0.53  thf('8', plain, (((v6_relat_2 @ sk_C_1) | ~ (v2_wellord1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain, ((v2_wellord1 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain, ((v6_relat_2 @ sk_C_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.20/0.53          | ((sk_A) = (X0))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_1)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '5', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.20/0.53        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)
% 0.20/0.53        | ((sk_A) = (sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.53  thf('13', plain, (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((((sk_A) = (sk_B_1))
% 0.20/0.53        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_A) @ sk_C_1))),
% 0.20/0.53      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf(d1_wellord1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i,C:$i]:
% 0.20/0.53         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.20/0.53           ( ![D:$i]:
% 0.20/0.53             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.53               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i, X8 : $i]:
% 0.20/0.53         (((X6) != (k1_wellord1 @ X5 @ X4))
% 0.20/0.53          | (r2_hidden @ X8 @ X6)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X8 @ X4) @ X5)
% 0.20/0.53          | ((X8) = (X4))
% 0.20/0.53          | ~ (v1_relat_1 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X5)
% 0.20/0.53          | ((X8) = (X4))
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X8 @ X4) @ X5)
% 0.20/0.53          | (r2_hidden @ X8 @ (k1_wellord1 @ X5 @ X4)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((((sk_A) = (sk_B_1))
% 0.20/0.53        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.20/0.53        | ((sk_B_1) = (sk_A))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.53  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((((sk_A) = (sk_B_1))
% 0.20/0.53        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.20/0.53        | ((sk_B_1) = (sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.20/0.53        | ((sk_A) = (sk_B_1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X16 : $i]:
% 0.20/0.53         (((X16) != (sk_B_1))
% 0.20/0.53          | ~ (r2_hidden @ X16 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('22', plain, (~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))),
% 0.20/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.53  thf('23', plain, (((sk_A) = (sk_B_1))),
% 0.20/0.53      inference('clc', [status(thm)], ['20', '22'])).
% 0.20/0.53  thf('24', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.53  thf(t37_wellord1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.53           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.20/0.53         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.53           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (v2_wellord1 @ X13)
% 0.20/0.53          | ~ (r2_hidden @ X14 @ (k3_relat_1 @ X13))
% 0.20/0.53          | ~ (r2_hidden @ X15 @ (k3_relat_1 @ X13))
% 0.20/0.53          | ~ (r1_tarski @ (k1_wellord1 @ X13 @ X14) @ 
% 0.20/0.53               (k1_wellord1 @ X13 @ X15))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ X13)
% 0.20/0.53          | ~ (v1_relat_1 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X1)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ X1))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ X1))
% 0.20/0.53          | ~ (v2_wellord1 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v2_wellord1 @ X1)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ X1))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1))),
% 0.20/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.53        | (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_1)
% 0.20/0.53        | ~ (v2_wellord1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '29'])).
% 0.20/0.53  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain, ((v2_wellord1 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.20/0.53  thf('34', plain, ($false),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '23', '33'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
