%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tIkPiOFrvl

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  69 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  312 ( 545 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X2 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('20',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('21',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tIkPiOFrvl
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:14:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 188 iterations in 0.130s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.58  thf(t172_relat_1, conjecture,
% 0.21/0.58    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.21/0.58  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.58  thf('1', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.58  thf(t3_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.58  thf(t166_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ C ) =>
% 0.21/0.58       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.21/0.58         ( ?[D:$i]:
% 0.21/0.58           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.58             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.21/0.58             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.21/0.58          | (r2_hidden @ (k4_tarski @ X12 @ (sk_D @ X13 @ X11 @ X12)) @ X13)
% 0.21/0.58          | ~ (v1_relat_1 @ X13))),
% 0.21/0.58      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.58          | ~ (v1_relat_1 @ X1)
% 0.21/0.58          | (r2_hidden @ 
% 0.21/0.58             (k4_tarski @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.21/0.58              (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.21/0.58             X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.58  thf(t7_tarski, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ~( ( r2_hidden @ A @ B ) & 
% 0.21/0.58          ( ![C:$i]:
% 0.21/0.58            ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.58                 ( ![D:$i]:
% 0.21/0.58                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7) @ X7))),
% 0.21/0.58      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.21/0.58          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf(t7_xboole_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.58          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.58          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.58          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((X0) = (k1_xboole_0))
% 0.21/0.58          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.58          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((X0) = (k1_xboole_0))
% 0.21/0.58          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.58          | ((X0) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((r2_hidden @ (sk_C_1 @ X1) @ X1)
% 0.21/0.58          | ~ (v1_relat_1 @ X1)
% 0.21/0.58          | ((k10_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['6', '12'])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((r2_hidden @ (sk_C_1 @ X1) @ X1)
% 0.21/0.58          | ~ (v1_relat_1 @ X1)
% 0.21/0.58          | ((k10_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['6', '12'])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.58          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.58          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (((k10_relat_1 @ X0 @ X2) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.58          | ~ (r2_hidden @ (sk_C_1 @ X0) @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (((k10_relat_1 @ X0 @ X2) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k10_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.58          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ((k10_relat_1 @ X0 @ X2) = (k1_xboole_0)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.58          | ((k10_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '18'])).
% 0.21/0.58  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.58  thf('20', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.58  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.58  thf('21', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.58  thf('22', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.58      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.58          | ((k10_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.58      inference('condensation', [status(thm)], ['23'])).
% 0.21/0.58  thf('25', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['0', '24'])).
% 0.21/0.58  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
