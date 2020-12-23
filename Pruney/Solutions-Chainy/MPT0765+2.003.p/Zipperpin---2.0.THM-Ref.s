%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rENJfa9sgd

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  97 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   17
%              Number of atoms          :  444 (1179 expanded)
%              Number of equality atoms :   19 (  43 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k3_relat_1 @ X6 ) @ ( k3_relat_1 @ X5 ) )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t10_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
              & ( B != k1_xboole_0 )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( r2_hidden @ D @ B )
                       => ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X9: $i] :
      ( ~ ( v2_wellord1 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X7 ) @ X9 )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t11_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ~ ( ( v2_wellord1 @ A )
          & ( ( k3_relat_1 @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
                & ! [C: $i] :
                    ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                   => ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ~ ( ( v2_wellord1 @ A )
            & ( ( k3_relat_1 @ A )
             != k1_xboole_0 )
            & ! [B: $i] :
                ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
                  & ! [C: $i] :
                      ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                     => ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord1])).

thf('11',plain,(
    ! [X10: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_2 @ X10 ) @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v2_wellord1 @ sk_A )
    | ( r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ( k3_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_wellord1 @ X7 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X9 @ X7 ) @ X8 ) @ X7 )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 ) @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 ) @ X1 ) @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( sk_C_2 @ ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( sk_C_2 @ ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ( k3_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( sk_C_2 @ ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ ( sk_C_2 @ X10 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ~ ( r2_hidden @ ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k3_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ( k3_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rENJfa9sgd
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 39 iterations in 0.027s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.21/0.46  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.46  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.46  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.46  thf(d3_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.46           ( ![C:$i,D:$i]:
% 0.21/0.46             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.21/0.46               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 0.21/0.46          | (r1_tarski @ X1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.21/0.46          | (r1_tarski @ X1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X0)
% 0.21/0.46          | (r1_tarski @ X0 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | (r1_tarski @ X0 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain, (![X0 : $i]: ((r1_tarski @ X0 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.46  thf(t31_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( v1_relat_1 @ B ) =>
% 0.21/0.46           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X5)
% 0.21/0.46          | (r1_tarski @ (k3_relat_1 @ X6) @ (k3_relat_1 @ X5))
% 0.21/0.46          | ~ (r1_tarski @ X6 @ X5)
% 0.21/0.46          | ~ (v1_relat_1 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | (r1_tarski @ (k3_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r1_tarski @ (k3_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.46  thf(t10_wellord1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ( v2_wellord1 @ A ) =>
% 0.21/0.46         ( ![B:$i]:
% 0.21/0.46           ( ~( ( r1_tarski @ B @ ( k3_relat_1 @ A ) ) & 
% 0.21/0.46                ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46                ( ![C:$i]:
% 0.21/0.46                  ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.46                       ( ![D:$i]:
% 0.21/0.46                         ( ( r2_hidden @ D @ B ) =>
% 0.21/0.46                           ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X7 : $i, X9 : $i]:
% 0.21/0.46         (~ (v2_wellord1 @ X7)
% 0.21/0.46          | (r2_hidden @ (sk_C_1 @ X9 @ X7) @ X9)
% 0.21/0.46          | ((X9) = (k1_xboole_0))
% 0.21/0.46          | ~ (r1_tarski @ X9 @ (k3_relat_1 @ X7))
% 0.21/0.46          | ~ (v1_relat_1 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t10_wellord1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.46          | (r2_hidden @ (sk_C_1 @ (k3_relat_1 @ X0) @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.46          | ~ (v2_wellord1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v2_wellord1 @ X0)
% 0.21/0.46          | (r2_hidden @ (sk_C_1 @ (k3_relat_1 @ X0) @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.46          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v2_wellord1 @ X0)
% 0.21/0.46          | (r2_hidden @ (sk_C_1 @ (k3_relat_1 @ X0) @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.46          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.46  thf(t11_wellord1, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ~( ( v2_wellord1 @ A ) & ( ( k3_relat_1 @ A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46            ( ![B:$i]:
% 0.21/0.46              ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.21/0.46                   ( ![C:$i]:
% 0.21/0.46                     ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) =>
% 0.21/0.46                       ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( v1_relat_1 @ A ) =>
% 0.21/0.46          ( ~( ( v2_wellord1 @ A ) & 
% 0.21/0.46               ( ( k3_relat_1 @ A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46               ( ![B:$i]:
% 0.21/0.46                 ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.21/0.46                      ( ![C:$i]:
% 0.21/0.46                        ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) =>
% 0.21/0.46                          ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t11_wellord1])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X10 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X10 @ (k3_relat_1 @ sk_A))
% 0.21/0.46          | (r2_hidden @ (sk_C_2 @ X10) @ (k3_relat_1 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.46        | ((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.46        | ~ (v2_wellord1 @ sk_A)
% 0.21/0.46        | (r2_hidden @ (sk_C_2 @ (sk_C_1 @ (k3_relat_1 @ sk_A) @ sk_A)) @ 
% 0.21/0.46           (k3_relat_1 @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('14', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      ((((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.46        | (r2_hidden @ (sk_C_2 @ (sk_C_1 @ (k3_relat_1 @ sk_A) @ sk_A)) @ 
% 0.21/0.46           (k3_relat_1 @ sk_A)))),
% 0.21/0.46      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.46  thf('16', plain, (((k3_relat_1 @ sk_A) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      ((r2_hidden @ (sk_C_2 @ (sk_C_1 @ (k3_relat_1 @ sk_A) @ sk_A)) @ 
% 0.21/0.46        (k3_relat_1 @ sk_A))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r1_tarski @ (k3_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.46         (~ (v2_wellord1 @ X7)
% 0.21/0.46          | ~ (r2_hidden @ X8 @ X9)
% 0.21/0.46          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X9 @ X7) @ X8) @ X7)
% 0.21/0.46          | ((X9) = (k1_xboole_0))
% 0.21/0.46          | ~ (r1_tarski @ X9 @ (k3_relat_1 @ X7))
% 0.21/0.46          | ~ (v1_relat_1 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t10_wellord1])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.46          | (r2_hidden @ 
% 0.21/0.46             (k4_tarski @ (sk_C_1 @ (k3_relat_1 @ X0) @ X0) @ X1) @ X0)
% 0.21/0.46          | ~ (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.21/0.46          | ~ (v2_wellord1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (v2_wellord1 @ X0)
% 0.21/0.46          | ~ (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.21/0.46          | (r2_hidden @ 
% 0.21/0.46             (k4_tarski @ (sk_C_1 @ (k3_relat_1 @ X0) @ X0) @ X1) @ X0)
% 0.21/0.46          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.46        | ((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.46        | (r2_hidden @ 
% 0.21/0.46           (k4_tarski @ (sk_C_1 @ (k3_relat_1 @ sk_A) @ sk_A) @ 
% 0.21/0.46            (sk_C_2 @ (sk_C_1 @ (k3_relat_1 @ sk_A) @ sk_A))) @ 
% 0.21/0.46           sk_A)
% 0.21/0.46        | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['17', '21'])).
% 0.21/0.46  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('24', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      ((((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.46        | (r2_hidden @ 
% 0.21/0.46           (k4_tarski @ (sk_C_1 @ (k3_relat_1 @ sk_A) @ sk_A) @ 
% 0.21/0.46            (sk_C_2 @ (sk_C_1 @ (k3_relat_1 @ sk_A) @ sk_A))) @ 
% 0.21/0.46           sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.46  thf('26', plain, (((k3_relat_1 @ sk_A) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      ((r2_hidden @ 
% 0.21/0.46        (k4_tarski @ (sk_C_1 @ (k3_relat_1 @ sk_A) @ sk_A) @ 
% 0.21/0.46         (sk_C_2 @ (sk_C_1 @ (k3_relat_1 @ sk_A) @ sk_A))) @ 
% 0.21/0.46        sk_A)),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.21/0.46  thf('28', plain,
% 0.21/0.46      (![X10 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X10 @ (k3_relat_1 @ sk_A))
% 0.21/0.46          | ~ (r2_hidden @ (k4_tarski @ X10 @ (sk_C_2 @ X10)) @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('29', plain,
% 0.21/0.46      (~ (r2_hidden @ (sk_C_1 @ (k3_relat_1 @ sk_A) @ sk_A) @ 
% 0.21/0.46          (k3_relat_1 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.46  thf('30', plain,
% 0.21/0.46      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.46        | ((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.46        | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '29'])).
% 0.21/0.46  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('32', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('33', plain, (((k3_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.46  thf('34', plain, (((k3_relat_1 @ sk_A) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('35', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
