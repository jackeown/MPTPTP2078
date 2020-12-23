%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SeoCaZ7hxW

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:04 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :   17
%              Number of atoms          :  429 ( 594 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

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

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t91_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ X0 )
      | ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('20',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X7 ) ) )
      | ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = X0 ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SeoCaZ7hxW
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 123 iterations in 0.138s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.59  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.36/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.59  thf(t2_tarski, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.36/0.59       ( ( A ) = ( B ) ) ))).
% 0.36/0.59  thf('0', plain,
% 0.36/0.59      (![X4 : $i, X5 : $i]:
% 0.36/0.59         (((X5) = (X4))
% 0.36/0.59          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.36/0.59          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_tarski])).
% 0.36/0.59  thf(d3_tarski, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.59  thf('1', plain,
% 0.36/0.59      (![X1 : $i, X3 : $i]:
% 0.36/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      (![X1 : $i, X3 : $i]:
% 0.36/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.59  thf(t91_relat_1, conjecture,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( v1_relat_1 @ B ) =>
% 0.36/0.59       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.59         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i,B:$i]:
% 0.36/0.59        ( ( v1_relat_1 @ B ) =>
% 0.36/0.59          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.59            ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t91_relat_1])).
% 0.36/0.59  thf('3', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.59          | (r2_hidden @ X0 @ X2)
% 0.36/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.59  thf('6', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_tarski @ sk_A @ X0)
% 0.36/0.59          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['2', '5'])).
% 0.36/0.59  thf(t86_relat_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( v1_relat_1 @ C ) =>
% 0.36/0.59       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.36/0.59         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X6 @ X7)
% 0.36/0.59          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X8))
% 0.36/0.59          | (r2_hidden @ X6 @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X7)))
% 0.36/0.59          | ~ (v1_relat_1 @ X8))),
% 0.36/0.59      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((r1_tarski @ sk_A @ X0)
% 0.36/0.59          | ~ (v1_relat_1 @ sk_B)
% 0.36/0.59          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.36/0.59             (k1_relat_1 @ (k7_relat_1 @ sk_B @ X1)))
% 0.36/0.59          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.59  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('10', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((r1_tarski @ sk_A @ X0)
% 0.36/0.59          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.36/0.59             (k1_relat_1 @ (k7_relat_1 @ sk_B @ X1)))
% 0.36/0.59          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1))),
% 0.36/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_tarski @ sk_A @ X0)
% 0.36/0.59          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.36/0.59             (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.36/0.59          | (r1_tarski @ sk_A @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['1', '10'])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.36/0.59           (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.36/0.59          | (r1_tarski @ sk_A @ X0))),
% 0.36/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      (![X1 : $i, X3 : $i]:
% 0.36/0.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.59  thf('14', plain,
% 0.36/0.59      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.36/0.59        | (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.59          | (r2_hidden @ X0 @ X2)
% 0.36/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.59  thf('17', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r2_hidden @ X0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.36/0.59          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r2_hidden @ (sk_C_1 @ sk_A @ X0) @ X0)
% 0.36/0.59          | ((X0) = (sk_A))
% 0.36/0.59          | (r2_hidden @ (sk_C_1 @ sk_A @ X0) @ 
% 0.36/0.59             (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['0', '17'])).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.36/0.59        | (r2_hidden @ 
% 0.36/0.59           (sk_C_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) @ 
% 0.36/0.59           (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.36/0.59      inference('eq_fact', [status(thm)], ['18'])).
% 0.36/0.59  thf('20', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      ((r2_hidden @ 
% 0.36/0.59        (sk_C_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) @ 
% 0.36/0.59        (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      (![X4 : $i, X5 : $i]:
% 0.36/0.59         (((X5) = (X4))
% 0.36/0.59          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.36/0.59          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_tarski])).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X6 @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X7)))
% 0.36/0.59          | (r2_hidden @ X6 @ X7)
% 0.36/0.59          | ~ (v1_relat_1 @ X8))),
% 0.36/0.59      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.36/0.59  thf('24', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((r2_hidden @ (sk_C_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.36/0.59           X2)
% 0.36/0.59          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (X2))
% 0.36/0.59          | ~ (v1_relat_1 @ X1)
% 0.36/0.59          | (r2_hidden @ 
% 0.36/0.59             (sk_C_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.59  thf('25', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((r2_hidden @ (sk_C_1 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.36/0.59           X0)
% 0.36/0.59          | ~ (v1_relat_1 @ X1)
% 0.36/0.59          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (X0)))),
% 0.36/0.59      inference('eq_fact', [status(thm)], ['24'])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      (![X4 : $i, X5 : $i]:
% 0.36/0.59         (((X5) = (X4))
% 0.36/0.59          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.36/0.59          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_tarski])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (X0))
% 0.36/0.59          | ~ (v1_relat_1 @ X1)
% 0.36/0.59          | ~ (r2_hidden @ 
% 0.36/0.59               (sk_C_1 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.36/0.59               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.36/0.59          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (X0)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (r2_hidden @ 
% 0.36/0.59             (sk_C_1 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.36/0.59             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.36/0.59          | ~ (v1_relat_1 @ X1)
% 0.36/0.59          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (X0)))),
% 0.36/0.59      inference('simplify', [status(thm)], ['27'])).
% 0.36/0.59  thf('29', plain,
% 0.36/0.59      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.36/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['21', '28'])).
% 0.36/0.59  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('31', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.59  thf('32', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('33', plain, ($false),
% 0.36/0.59      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
