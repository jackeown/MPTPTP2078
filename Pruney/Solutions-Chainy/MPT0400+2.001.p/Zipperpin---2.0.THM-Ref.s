%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gRg6ZP0usw

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:01 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   16
%              Number of atoms          :  443 ( 686 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t23_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_setfam_1 @ A @ B )
        & ( r1_setfam_1 @ B @ C ) )
     => ( r1_setfam_1 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_setfam_1 @ A @ B )
          & ( r1_setfam_1 @ B @ C ) )
       => ( r1_setfam_1 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t23_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_setfam_1 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('2',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_D @ X4 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_setfam_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_setfam_1 @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_D @ X4 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_setfam_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_setfam_1 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ ( sk_D @ X4 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_setfam_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r1_setfam_1 @ X0 @ X2 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_D @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 @ sk_A ) ) @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    r1_setfam_1 @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ ( sk_D @ X4 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_setfam_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ~ ( r1_setfam_1 @ sk_B @ X1 )
      | ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_C_2 ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_C_2 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 @ sk_A ) ) @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_C_2 ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 @ sk_A ) ) @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_C_2 ) )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ X1 )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_C_2 ) )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_C_2 ) )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_setfam_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X7 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_C_2 ) @ X0 )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( sk_D @ ( sk_C_1 @ X0 @ sk_A ) @ sk_B ) @ sk_C_2 ) @ X0 )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( r1_setfam_1 @ sk_A @ sk_C_2 )
    | ( r1_setfam_1 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['9','33'])).

thf('35',plain,(
    r1_setfam_1 @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gRg6ZP0usw
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.64/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.83  % Solved by: fo/fo7.sh
% 0.64/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.83  % done 399 iterations in 0.379s
% 0.64/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.83  % SZS output start Refutation
% 0.64/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.64/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.64/0.83  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.64/0.83  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.64/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.83  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.64/0.83  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.64/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.83  thf(t23_setfam_1, conjecture,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( ( r1_setfam_1 @ A @ B ) & ( r1_setfam_1 @ B @ C ) ) =>
% 0.64/0.83       ( r1_setfam_1 @ A @ C ) ))).
% 0.64/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.64/0.83        ( ( ( r1_setfam_1 @ A @ B ) & ( r1_setfam_1 @ B @ C ) ) =>
% 0.64/0.83          ( r1_setfam_1 @ A @ C ) ) )),
% 0.64/0.83    inference('cnf.neg', [status(esa)], [t23_setfam_1])).
% 0.64/0.83  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ sk_C_2)),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(d2_setfam_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.64/0.83       ( ![C:$i]:
% 0.64/0.83         ( ~( ( r2_hidden @ C @ A ) & 
% 0.64/0.83              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.64/0.83  thf('1', plain,
% 0.64/0.83      (![X6 : $i, X7 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ X6))),
% 0.64/0.83      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.64/0.83  thf('2', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf('3', plain,
% 0.64/0.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.64/0.83         ((r2_hidden @ (sk_D @ X4 @ X5) @ X5)
% 0.64/0.83          | ~ (r2_hidden @ X4 @ X6)
% 0.64/0.83          | ~ (r1_setfam_1 @ X6 @ X5))),
% 0.64/0.83      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.64/0.83  thf('4', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ (sk_D @ X0 @ sk_B) @ sk_B))),
% 0.64/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.64/0.83  thf('5', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ sk_A @ X0)
% 0.64/0.83          | (r2_hidden @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_B))),
% 0.64/0.83      inference('sup-', [status(thm)], ['1', '4'])).
% 0.64/0.83  thf('6', plain, ((r1_setfam_1 @ sk_B @ sk_C_2)),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf('7', plain,
% 0.64/0.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.64/0.83         ((r2_hidden @ (sk_D @ X4 @ X5) @ X5)
% 0.64/0.83          | ~ (r2_hidden @ X4 @ X6)
% 0.64/0.83          | ~ (r1_setfam_1 @ X6 @ X5))),
% 0.64/0.83      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.64/0.83  thf('8', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (~ (r2_hidden @ X0 @ sk_B)
% 0.64/0.83          | (r2_hidden @ (sk_D @ X0 @ sk_C_2) @ sk_C_2))),
% 0.64/0.83      inference('sup-', [status(thm)], ['6', '7'])).
% 0.64/0.83  thf('9', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ sk_A @ X0)
% 0.64/0.83          | (r2_hidden @ 
% 0.64/0.83             (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_C_2) @ sk_C_2))),
% 0.64/0.83      inference('sup-', [status(thm)], ['5', '8'])).
% 0.64/0.83  thf(d3_tarski, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( r1_tarski @ A @ B ) <=>
% 0.64/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.64/0.83  thf('10', plain,
% 0.64/0.83      (![X1 : $i, X3 : $i]:
% 0.64/0.83         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.64/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.64/0.83  thf('11', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf('12', plain,
% 0.64/0.83      (![X6 : $i, X7 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ X6))),
% 0.64/0.83      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.64/0.83  thf('13', plain,
% 0.64/0.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.64/0.83         ((r1_tarski @ X4 @ (sk_D @ X4 @ X5))
% 0.64/0.83          | ~ (r2_hidden @ X4 @ X6)
% 0.64/0.83          | ~ (r1_setfam_1 @ X6 @ X5))),
% 0.64/0.83      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.64/0.83  thf('14', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ X0 @ X1)
% 0.64/0.83          | ~ (r1_setfam_1 @ X0 @ X2)
% 0.64/0.83          | (r1_tarski @ (sk_C_1 @ X1 @ X0) @ (sk_D @ (sk_C_1 @ X1 @ X0) @ X2)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['12', '13'])).
% 0.64/0.83  thf('15', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ 
% 0.64/0.83           (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B))
% 0.64/0.83          | (r1_setfam_1 @ sk_A @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['11', '14'])).
% 0.64/0.83  thf('16', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.83         (~ (r2_hidden @ X0 @ X1)
% 0.64/0.83          | (r2_hidden @ X0 @ X2)
% 0.64/0.83          | ~ (r1_tarski @ X1 @ X2))),
% 0.64/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.64/0.83  thf('17', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ sk_A @ X0)
% 0.64/0.83          | (r2_hidden @ X1 @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B))
% 0.64/0.83          | ~ (r2_hidden @ X1 @ (sk_C_1 @ X0 @ sk_A)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.64/0.83  thf('18', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         ((r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ X1)
% 0.64/0.83          | (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0 @ sk_A)) @ 
% 0.64/0.83             (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B))
% 0.64/0.83          | (r1_setfam_1 @ sk_A @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['10', '17'])).
% 0.64/0.83  thf('19', plain, ((r1_setfam_1 @ sk_B @ sk_C_2)),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf('20', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ sk_A @ X0)
% 0.64/0.83          | (r2_hidden @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_B))),
% 0.64/0.83      inference('sup-', [status(thm)], ['1', '4'])).
% 0.64/0.83  thf('21', plain,
% 0.64/0.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.64/0.83         ((r1_tarski @ X4 @ (sk_D @ X4 @ X5))
% 0.64/0.83          | ~ (r2_hidden @ X4 @ X6)
% 0.64/0.83          | ~ (r1_setfam_1 @ X6 @ X5))),
% 0.64/0.83      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.64/0.83  thf('22', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ sk_A @ X0)
% 0.64/0.83          | ~ (r1_setfam_1 @ sk_B @ X1)
% 0.64/0.83          | (r1_tarski @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ 
% 0.64/0.83             (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ X1)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.64/0.83  thf('23', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r1_tarski @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ 
% 0.64/0.83           (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_C_2))
% 0.64/0.83          | (r1_setfam_1 @ sk_A @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['19', '22'])).
% 0.64/0.83  thf('24', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.83         (~ (r2_hidden @ X0 @ X1)
% 0.64/0.83          | (r2_hidden @ X0 @ X2)
% 0.64/0.83          | ~ (r1_tarski @ X1 @ X2))),
% 0.64/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.64/0.83  thf('25', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ sk_A @ X0)
% 0.64/0.83          | (r2_hidden @ X1 @ 
% 0.64/0.83             (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_C_2))
% 0.64/0.83          | ~ (r2_hidden @ X1 @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['23', '24'])).
% 0.64/0.83  thf('26', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ sk_A @ X0)
% 0.64/0.83          | (r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ X1)
% 0.64/0.83          | (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0 @ sk_A)) @ 
% 0.64/0.83             (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_C_2))
% 0.64/0.83          | (r1_setfam_1 @ sk_A @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['18', '25'])).
% 0.64/0.83  thf('27', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         ((r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0 @ sk_A)) @ 
% 0.64/0.83           (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_C_2))
% 0.64/0.83          | (r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ X1)
% 0.64/0.83          | (r1_setfam_1 @ sk_A @ X0))),
% 0.64/0.83      inference('simplify', [status(thm)], ['26'])).
% 0.64/0.83  thf('28', plain,
% 0.64/0.83      (![X1 : $i, X3 : $i]:
% 0.64/0.83         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.64/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.64/0.83  thf('29', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ sk_A @ X0)
% 0.64/0.83          | (r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ 
% 0.64/0.83             (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_C_2))
% 0.64/0.83          | (r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ 
% 0.64/0.83             (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_C_2)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['27', '28'])).
% 0.64/0.83  thf('30', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r1_tarski @ (sk_C_1 @ X0 @ sk_A) @ 
% 0.64/0.83           (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_C_2))
% 0.64/0.83          | (r1_setfam_1 @ sk_A @ X0))),
% 0.64/0.83      inference('simplify', [status(thm)], ['29'])).
% 0.64/0.83  thf('31', plain,
% 0.64/0.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ X6 @ X7)
% 0.64/0.83          | ~ (r2_hidden @ X8 @ X7)
% 0.64/0.83          | ~ (r1_tarski @ (sk_C_1 @ X7 @ X6) @ X8))),
% 0.64/0.83      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.64/0.83  thf('32', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r1_setfam_1 @ sk_A @ X0)
% 0.64/0.83          | ~ (r2_hidden @ 
% 0.64/0.83               (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_C_2) @ X0)
% 0.64/0.83          | (r1_setfam_1 @ sk_A @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['30', '31'])).
% 0.64/0.83  thf('33', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (~ (r2_hidden @ 
% 0.64/0.83             (sk_D @ (sk_D @ (sk_C_1 @ X0 @ sk_A) @ sk_B) @ sk_C_2) @ X0)
% 0.64/0.83          | (r1_setfam_1 @ sk_A @ X0))),
% 0.64/0.83      inference('simplify', [status(thm)], ['32'])).
% 0.64/0.83  thf('34', plain,
% 0.64/0.83      (((r1_setfam_1 @ sk_A @ sk_C_2) | (r1_setfam_1 @ sk_A @ sk_C_2))),
% 0.64/0.83      inference('sup-', [status(thm)], ['9', '33'])).
% 0.64/0.83  thf('35', plain, ((r1_setfam_1 @ sk_A @ sk_C_2)),
% 0.64/0.83      inference('simplify', [status(thm)], ['34'])).
% 0.64/0.83  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.64/0.83  
% 0.64/0.83  % SZS output end Refutation
% 0.64/0.83  
% 0.64/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
