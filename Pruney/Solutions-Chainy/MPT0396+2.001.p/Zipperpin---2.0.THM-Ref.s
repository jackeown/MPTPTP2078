%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LhpE2tr2DV

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:54 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  406 ( 554 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t18_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_setfam_1 @ A @ B )
       => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
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

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ X5 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('3',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X11 @ X12 ) @ X12 )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r1_setfam_1 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X5 ) )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('11',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ ( sk_D_2 @ X11 @ X12 ) )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r1_setfam_1 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r1_setfam_1 @ X0 @ X2 )
      | ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ ( sk_D_2 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ ( sk_D_2 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ ( sk_D_2 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ ( sk_D_2 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_2 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) )
    | ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LhpE2tr2DV
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:39:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.25/2.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.25/2.51  % Solved by: fo/fo7.sh
% 2.25/2.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.25/2.51  % done 555 iterations in 2.068s
% 2.25/2.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.25/2.51  % SZS output start Refutation
% 2.25/2.51  thf(sk_B_type, type, sk_B: $i).
% 2.25/2.51  thf(sk_A_type, type, sk_A: $i).
% 2.25/2.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.25/2.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.25/2.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.25/2.51  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 2.25/2.51  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 2.25/2.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 2.25/2.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.25/2.51  thf(t18_setfam_1, conjecture,
% 2.25/2.51    (![A:$i,B:$i]:
% 2.25/2.51     ( ( r1_setfam_1 @ A @ B ) =>
% 2.25/2.51       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 2.25/2.51  thf(zf_stmt_0, negated_conjecture,
% 2.25/2.51    (~( ![A:$i,B:$i]:
% 2.25/2.51        ( ( r1_setfam_1 @ A @ B ) =>
% 2.25/2.51          ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 2.25/2.51    inference('cnf.neg', [status(esa)], [t18_setfam_1])).
% 2.25/2.51  thf('0', plain, (~ (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 2.25/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.51  thf(d3_tarski, axiom,
% 2.25/2.51    (![A:$i,B:$i]:
% 2.25/2.51     ( ( r1_tarski @ A @ B ) <=>
% 2.25/2.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.25/2.51  thf('1', plain,
% 2.25/2.51      (![X1 : $i, X3 : $i]:
% 2.25/2.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.25/2.51      inference('cnf', [status(esa)], [d3_tarski])).
% 2.25/2.51  thf(d4_tarski, axiom,
% 2.25/2.51    (![A:$i,B:$i]:
% 2.25/2.51     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 2.25/2.51       ( ![C:$i]:
% 2.25/2.51         ( ( r2_hidden @ C @ B ) <=>
% 2.25/2.51           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 2.25/2.51  thf('2', plain,
% 2.25/2.51      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.25/2.51         (~ (r2_hidden @ X8 @ X7)
% 2.25/2.51          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ X5)
% 2.25/2.51          | ((X7) != (k3_tarski @ X5)))),
% 2.25/2.51      inference('cnf', [status(esa)], [d4_tarski])).
% 2.25/2.51  thf('3', plain,
% 2.25/2.51      (![X5 : $i, X8 : $i]:
% 2.25/2.51         ((r2_hidden @ (sk_D_1 @ X8 @ X5) @ X5)
% 2.25/2.51          | ~ (r2_hidden @ X8 @ (k3_tarski @ X5)))),
% 2.25/2.51      inference('simplify', [status(thm)], ['2'])).
% 2.25/2.51  thf('4', plain,
% 2.25/2.51      (![X0 : $i, X1 : $i]:
% 2.25/2.51         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 2.25/2.51          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ X0))),
% 2.25/2.51      inference('sup-', [status(thm)], ['1', '3'])).
% 2.25/2.51  thf('5', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 2.25/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.51  thf(d2_setfam_1, axiom,
% 2.25/2.51    (![A:$i,B:$i]:
% 2.25/2.51     ( ( r1_setfam_1 @ A @ B ) <=>
% 2.25/2.51       ( ![C:$i]:
% 2.25/2.51         ( ~( ( r2_hidden @ C @ A ) & 
% 2.25/2.51              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 2.25/2.51  thf('6', plain,
% 2.25/2.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.25/2.51         ((r2_hidden @ (sk_D_2 @ X11 @ X12) @ X12)
% 2.25/2.51          | ~ (r2_hidden @ X11 @ X13)
% 2.25/2.51          | ~ (r1_setfam_1 @ X13 @ X12))),
% 2.25/2.51      inference('cnf', [status(esa)], [d2_setfam_1])).
% 2.25/2.51  thf('7', plain,
% 2.25/2.51      (![X0 : $i]:
% 2.25/2.51         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ (sk_D_2 @ X0 @ sk_B) @ sk_B))),
% 2.25/2.51      inference('sup-', [status(thm)], ['5', '6'])).
% 2.25/2.51  thf('8', plain,
% 2.25/2.51      (![X0 : $i]:
% 2.25/2.51         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.25/2.51          | (r2_hidden @ 
% 2.25/2.51             (sk_D_2 @ (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A) @ 
% 2.25/2.51              sk_B) @ 
% 2.25/2.51             sk_B))),
% 2.25/2.51      inference('sup-', [status(thm)], ['4', '7'])).
% 2.25/2.51  thf('9', plain,
% 2.25/2.51      (![X1 : $i, X3 : $i]:
% 2.25/2.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.25/2.51      inference('cnf', [status(esa)], [d3_tarski])).
% 2.25/2.51  thf('10', plain,
% 2.25/2.51      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.25/2.51         (~ (r2_hidden @ X8 @ X7)
% 2.25/2.51          | (r2_hidden @ X8 @ (sk_D_1 @ X8 @ X5))
% 2.25/2.51          | ((X7) != (k3_tarski @ X5)))),
% 2.25/2.51      inference('cnf', [status(esa)], [d4_tarski])).
% 2.25/2.51  thf('11', plain,
% 2.25/2.51      (![X5 : $i, X8 : $i]:
% 2.25/2.51         ((r2_hidden @ X8 @ (sk_D_1 @ X8 @ X5))
% 2.25/2.51          | ~ (r2_hidden @ X8 @ (k3_tarski @ X5)))),
% 2.25/2.51      inference('simplify', [status(thm)], ['10'])).
% 2.25/2.51  thf('12', plain,
% 2.25/2.51      (![X0 : $i, X1 : $i]:
% 2.25/2.51         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 2.25/2.51          | (r2_hidden @ (sk_C @ X1 @ (k3_tarski @ X0)) @ 
% 2.25/2.51             (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0)))),
% 2.25/2.51      inference('sup-', [status(thm)], ['9', '11'])).
% 2.25/2.51  thf('13', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 2.25/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.51  thf('14', plain,
% 2.25/2.51      (![X0 : $i, X1 : $i]:
% 2.25/2.51         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 2.25/2.51          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ X0))),
% 2.25/2.51      inference('sup-', [status(thm)], ['1', '3'])).
% 2.25/2.51  thf('15', plain,
% 2.25/2.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.25/2.51         ((r1_tarski @ X11 @ (sk_D_2 @ X11 @ X12))
% 2.25/2.51          | ~ (r2_hidden @ X11 @ X13)
% 2.25/2.51          | ~ (r1_setfam_1 @ X13 @ X12))),
% 2.25/2.51      inference('cnf', [status(esa)], [d2_setfam_1])).
% 2.25/2.51  thf('16', plain,
% 2.25/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.51         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 2.25/2.51          | ~ (r1_setfam_1 @ X0 @ X2)
% 2.25/2.51          | (r1_tarski @ (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ 
% 2.25/2.51             (sk_D_2 @ (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ X2)))),
% 2.25/2.51      inference('sup-', [status(thm)], ['14', '15'])).
% 2.25/2.51  thf('17', plain,
% 2.25/2.51      (![X0 : $i]:
% 2.25/2.51         ((r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A) @ 
% 2.25/2.51           (sk_D_2 @ (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A) @ sk_B))
% 2.25/2.51          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 2.25/2.51      inference('sup-', [status(thm)], ['13', '16'])).
% 2.25/2.51  thf('18', plain,
% 2.25/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.51         (~ (r2_hidden @ X0 @ X1)
% 2.25/2.51          | (r2_hidden @ X0 @ X2)
% 2.25/2.51          | ~ (r1_tarski @ X1 @ X2))),
% 2.25/2.51      inference('cnf', [status(esa)], [d3_tarski])).
% 2.25/2.51  thf('19', plain,
% 2.25/2.51      (![X0 : $i, X1 : $i]:
% 2.25/2.51         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.25/2.51          | (r2_hidden @ X1 @ 
% 2.25/2.51             (sk_D_2 @ (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A) @ 
% 2.25/2.51              sk_B))
% 2.25/2.51          | ~ (r2_hidden @ X1 @ 
% 2.25/2.51               (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A)))),
% 2.25/2.51      inference('sup-', [status(thm)], ['17', '18'])).
% 2.25/2.51  thf('20', plain,
% 2.25/2.51      (![X0 : $i]:
% 2.25/2.51         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.25/2.51          | (r2_hidden @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ 
% 2.25/2.51             (sk_D_2 @ (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A) @ 
% 2.25/2.51              sk_B))
% 2.25/2.51          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 2.25/2.51      inference('sup-', [status(thm)], ['12', '19'])).
% 2.25/2.51  thf('21', plain,
% 2.25/2.51      (![X0 : $i]:
% 2.25/2.51         ((r2_hidden @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ 
% 2.25/2.51           (sk_D_2 @ (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A) @ sk_B))
% 2.25/2.51          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 2.25/2.51      inference('simplify', [status(thm)], ['20'])).
% 2.25/2.51  thf('22', plain,
% 2.25/2.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.25/2.51         (~ (r2_hidden @ X4 @ X5)
% 2.25/2.51          | ~ (r2_hidden @ X6 @ X4)
% 2.25/2.51          | (r2_hidden @ X6 @ X7)
% 2.25/2.51          | ((X7) != (k3_tarski @ X5)))),
% 2.25/2.51      inference('cnf', [status(esa)], [d4_tarski])).
% 2.25/2.51  thf('23', plain,
% 2.25/2.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.25/2.51         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 2.25/2.51          | ~ (r2_hidden @ X6 @ X4)
% 2.25/2.51          | ~ (r2_hidden @ X4 @ X5))),
% 2.25/2.51      inference('simplify', [status(thm)], ['22'])).
% 2.25/2.51  thf('24', plain,
% 2.25/2.51      (![X0 : $i, X1 : $i]:
% 2.25/2.51         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.25/2.51          | ~ (r2_hidden @ 
% 2.25/2.51               (sk_D_2 @ (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A) @ 
% 2.25/2.51                sk_B) @ 
% 2.25/2.51               X1)
% 2.25/2.51          | (r2_hidden @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ (k3_tarski @ X1)))),
% 2.25/2.51      inference('sup-', [status(thm)], ['21', '23'])).
% 2.25/2.51  thf('25', plain,
% 2.25/2.51      (![X0 : $i]:
% 2.25/2.51         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 2.25/2.51          | (r2_hidden @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ (k3_tarski @ sk_B))
% 2.25/2.51          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 2.25/2.51      inference('sup-', [status(thm)], ['8', '24'])).
% 2.25/2.51  thf('26', plain,
% 2.25/2.51      (![X0 : $i]:
% 2.25/2.51         ((r2_hidden @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ (k3_tarski @ sk_B))
% 2.25/2.51          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 2.25/2.51      inference('simplify', [status(thm)], ['25'])).
% 2.25/2.51  thf('27', plain,
% 2.25/2.51      (![X1 : $i, X3 : $i]:
% 2.25/2.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.25/2.51      inference('cnf', [status(esa)], [d3_tarski])).
% 2.25/2.51  thf('28', plain,
% 2.25/2.51      (((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))
% 2.25/2.51        | (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 2.25/2.51      inference('sup-', [status(thm)], ['26', '27'])).
% 2.25/2.51  thf('29', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 2.25/2.51      inference('simplify', [status(thm)], ['28'])).
% 2.25/2.51  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 2.25/2.51  
% 2.25/2.51  % SZS output end Refutation
% 2.25/2.51  
% 2.25/2.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
