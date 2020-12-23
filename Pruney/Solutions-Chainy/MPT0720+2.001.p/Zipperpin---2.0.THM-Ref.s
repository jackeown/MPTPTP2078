%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tf7m8RoJho

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:34 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   59 (  85 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  402 ( 700 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t175_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B )
            & ( v5_funct_1 @ B @ A ) )
         => ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B )
              & ( v5_funct_1 @ B @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( X15 = k1_xboole_0 )
      | ( X15
       != ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_funct_1 @ X14 @ X13 )
        = k1_xboole_0 )
      | ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v5_funct_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v5_funct_1 @ X10 @ X11 )
      | ( r2_hidden @ ( k1_funct_1 @ X10 @ X12 ) @ ( k1_funct_1 @ X11 @ X12 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_funct_1 @ X2 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v5_funct_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','31','32','33'])).

thf('35',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tf7m8RoJho
% 0.16/0.38  % Computer   : n025.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 14:52:06 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.25/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.57  % Solved by: fo/fo7.sh
% 0.25/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.57  % done 115 iterations in 0.077s
% 0.25/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.57  % SZS output start Refutation
% 0.25/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.25/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.25/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.57  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.25/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.25/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.25/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.57  thf(t175_funct_1, conjecture,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.25/0.57       ( ![B:$i]:
% 0.25/0.57         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & ( v5_funct_1 @ B @ A ) ) =>
% 0.25/0.57           ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.25/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.57    (~( ![A:$i]:
% 0.25/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.25/0.57          ( ![B:$i]:
% 0.25/0.57            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & 
% 0.25/0.57                ( v5_funct_1 @ B @ A ) ) =>
% 0.25/0.57              ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.25/0.57    inference('cnf.neg', [status(esa)], [t175_funct_1])).
% 0.25/0.57  thf('0', plain,
% 0.25/0.57      (~ (r1_tarski @ (k1_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(d4_funct_1, axiom,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.25/0.57       ( ![B:$i,C:$i]:
% 0.25/0.57         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.25/0.57             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.25/0.57               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.25/0.57           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.25/0.57             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.25/0.57               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.25/0.57  thf('1', plain,
% 0.25/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.25/0.57         ((r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 0.25/0.57          | ((X15) = (k1_xboole_0))
% 0.25/0.57          | ((X15) != (k1_funct_1 @ X14 @ X13))
% 0.25/0.57          | ~ (v1_funct_1 @ X14)
% 0.25/0.57          | ~ (v1_relat_1 @ X14))),
% 0.25/0.57      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.25/0.57  thf('2', plain,
% 0.25/0.57      (![X13 : $i, X14 : $i]:
% 0.25/0.57         (~ (v1_relat_1 @ X14)
% 0.25/0.57          | ~ (v1_funct_1 @ X14)
% 0.25/0.57          | ((k1_funct_1 @ X14 @ X13) = (k1_xboole_0))
% 0.25/0.57          | (r2_hidden @ X13 @ (k1_relat_1 @ X14)))),
% 0.25/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.25/0.57  thf(d3_tarski, axiom,
% 0.25/0.57    (![A:$i,B:$i]:
% 0.25/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.25/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.25/0.57  thf('3', plain,
% 0.25/0.57      (![X6 : $i, X8 : $i]:
% 0.25/0.57         ((r1_tarski @ X6 @ X8) | ~ (r2_hidden @ (sk_C @ X8 @ X6) @ X8))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('4', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i]:
% 0.25/0.57         (((k1_funct_1 @ X0 @ (sk_C @ (k1_relat_1 @ X0) @ X1)) = (k1_xboole_0))
% 0.25/0.57          | ~ (v1_funct_1 @ X0)
% 0.25/0.57          | ~ (v1_relat_1 @ X0)
% 0.25/0.57          | (r1_tarski @ X1 @ (k1_relat_1 @ X0)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.57  thf('5', plain, ((v5_funct_1 @ sk_B_1 @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('6', plain,
% 0.25/0.57      (![X6 : $i, X8 : $i]:
% 0.25/0.57         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf(d20_funct_1, axiom,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.25/0.57       ( ![B:$i]:
% 0.25/0.57         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.25/0.57           ( ( v5_funct_1 @ B @ A ) <=>
% 0.25/0.57             ( ![C:$i]:
% 0.25/0.57               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.25/0.57                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.25/0.57  thf('7', plain,
% 0.25/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.25/0.57         (~ (v1_relat_1 @ X10)
% 0.25/0.57          | ~ (v1_funct_1 @ X10)
% 0.25/0.57          | ~ (v5_funct_1 @ X10 @ X11)
% 0.25/0.57          | (r2_hidden @ (k1_funct_1 @ X10 @ X12) @ (k1_funct_1 @ X11 @ X12))
% 0.25/0.57          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X10))
% 0.25/0.57          | ~ (v1_funct_1 @ X11)
% 0.25/0.57          | ~ (v1_relat_1 @ X11))),
% 0.25/0.57      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.25/0.57  thf('8', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.25/0.57          | ~ (v1_relat_1 @ X2)
% 0.25/0.57          | ~ (v1_funct_1 @ X2)
% 0.25/0.57          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0))) @ 
% 0.25/0.57             (k1_funct_1 @ X2 @ (sk_C @ X1 @ (k1_relat_1 @ X0))))
% 0.25/0.57          | ~ (v5_funct_1 @ X0 @ X2)
% 0.25/0.57          | ~ (v1_funct_1 @ X0)
% 0.25/0.57          | ~ (v1_relat_1 @ X0))),
% 0.25/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.25/0.57  thf('9', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         (~ (v1_relat_1 @ sk_B_1)
% 0.25/0.57          | ~ (v1_funct_1 @ sk_B_1)
% 0.25/0.57          | (r2_hidden @ 
% 0.25/0.57             (k1_funct_1 @ sk_B_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_B_1))) @ 
% 0.25/0.57             (k1_funct_1 @ sk_A @ (sk_C @ X0 @ (k1_relat_1 @ sk_B_1))))
% 0.25/0.57          | ~ (v1_funct_1 @ sk_A)
% 0.25/0.57          | ~ (v1_relat_1 @ sk_A)
% 0.25/0.57          | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ X0))),
% 0.25/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.25/0.57  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('11', plain, ((v1_funct_1 @ sk_B_1)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('12', plain, ((v1_funct_1 @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('14', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r2_hidden @ 
% 0.25/0.57           (k1_funct_1 @ sk_B_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_B_1))) @ 
% 0.25/0.57           (k1_funct_1 @ sk_A @ (sk_C @ X0 @ (k1_relat_1 @ sk_B_1))))
% 0.25/0.57          | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ X0))),
% 0.25/0.57      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.25/0.57  thf(d1_xboole_0, axiom,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.25/0.57  thf('15', plain,
% 0.25/0.57      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.25/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.25/0.57  thf('16', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ X0)
% 0.25/0.57          | ~ (v1_xboole_0 @ 
% 0.25/0.57               (k1_funct_1 @ sk_A @ (sk_C @ X0 @ (k1_relat_1 @ sk_B_1)))))),
% 0.25/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.25/0.57  thf('17', plain,
% 0.25/0.57      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.25/0.57        | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 0.25/0.57        | ~ (v1_relat_1 @ sk_A)
% 0.25/0.57        | ~ (v1_funct_1 @ sk_A)
% 0.25/0.57        | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['4', '16'])).
% 0.25/0.57  thf('18', plain,
% 0.25/0.57      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.25/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.25/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.25/0.57  thf('19', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.25/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.25/0.57  thf('20', plain,
% 0.25/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.25/0.57         (~ (r2_hidden @ X5 @ X6)
% 0.25/0.57          | (r2_hidden @ X5 @ X7)
% 0.25/0.57          | ~ (r1_tarski @ X6 @ X7))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('21', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i]:
% 0.25/0.57         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.25/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.25/0.57  thf('22', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.25/0.57      inference('sup-', [status(thm)], ['18', '21'])).
% 0.25/0.57  thf('23', plain,
% 0.25/0.57      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.25/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.25/0.57  thf(antisymmetry_r2_hidden, axiom,
% 0.25/0.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.25/0.57  thf('24', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.25/0.57      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.25/0.57  thf('25', plain,
% 0.25/0.57      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r2_hidden @ X0 @ (sk_B @ X0)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.25/0.57  thf('26', plain,
% 0.25/0.57      (((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (sk_B @ k1_xboole_0)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['22', '25'])).
% 0.25/0.57  thf('27', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.25/0.57      inference('sup-', [status(thm)], ['18', '21'])).
% 0.25/0.57  thf('28', plain,
% 0.25/0.57      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.25/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.25/0.57  thf('29', plain,
% 0.25/0.57      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.25/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.25/0.57  thf('30', plain,
% 0.25/0.57      (((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.25/0.57      inference('sup-', [status(thm)], ['26', '29'])).
% 0.25/0.57  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.57      inference('simplify', [status(thm)], ['30'])).
% 0.25/0.57  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('33', plain, ((v1_funct_1 @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('34', plain,
% 0.25/0.57      (((r1_tarski @ (k1_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 0.25/0.57        | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)))),
% 0.25/0.57      inference('demod', [status(thm)], ['17', '31', '32', '33'])).
% 0.25/0.57  thf('35', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))),
% 0.25/0.57      inference('simplify', [status(thm)], ['34'])).
% 0.25/0.57  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.25/0.57  
% 0.25/0.57  % SZS output end Refutation
% 0.25/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
