%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ad3b2sdSFh

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:24 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   52 (  67 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  449 ( 680 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t186_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
              & ( r1_tarski @ C @ B ) )
           => ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
                & ( r1_tarski @ C @ B ) )
             => ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_3 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X11 ) @ ( sk_D_1 @ X10 @ X11 ) ) @ X11 )
      | ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 )
      | ( r2_hidden @ X15 @ X18 )
      | ( X18
       != ( k1_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ ( k1_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X11 ) @ ( sk_D_1 @ X10 @ X11 ) ) @ X11 )
      | ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('12',plain,(
    r1_tarski @ sk_C_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_3 )
      | ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( sk_D_1 @ X0 @ sk_C_3 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( sk_D_1 @ X0 @ sk_C_3 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k7_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ D @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X4
       != ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X5 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( sk_D_1 @ X0 @ sk_C_3 ) ) @ ( k7_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( sk_D_1 @ X0 @ sk_C_3 ) ) @ ( k7_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_3 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( sk_D_1 @ X0 @ sk_C_3 ) ) @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_3 ) @ ( sk_D_1 @ X0 @ sk_C_3 ) ) @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X11 ) @ ( sk_D_1 @ X10 @ X11 ) ) @ X10 )
      | ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('29',plain,
    ( ( r1_tarski @ sk_C_3 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ( r1_tarski @ sk_C_3 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_tarski @ sk_C_3 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( r1_tarski @ sk_C_3 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_C_3 @ ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ad3b2sdSFh
% 0.15/0.37  % Computer   : n015.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 15:43:38 EST 2020
% 0.23/0.38  % CPUTime    : 
% 0.23/0.38  % Running portfolio for 600 s
% 0.23/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.58/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.78  % Solved by: fo/fo7.sh
% 0.58/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.78  % done 291 iterations in 0.291s
% 0.58/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.78  % SZS output start Refutation
% 0.58/0.78  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.58/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.78  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.58/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.78  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.58/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.78  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.58/0.78  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.58/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.78  thf(t186_relat_1, conjecture,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( v1_relat_1 @ B ) =>
% 0.58/0.78       ( ![C:$i]:
% 0.58/0.78         ( ( v1_relat_1 @ C ) =>
% 0.58/0.78           ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.58/0.78             ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.58/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.78    (~( ![A:$i,B:$i]:
% 0.58/0.78        ( ( v1_relat_1 @ B ) =>
% 0.58/0.78          ( ![C:$i]:
% 0.58/0.78            ( ( v1_relat_1 @ C ) =>
% 0.58/0.78              ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.58/0.78                  ( r1_tarski @ C @ B ) ) =>
% 0.58/0.78                ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ) )),
% 0.58/0.78    inference('cnf.neg', [status(esa)], [t186_relat_1])).
% 0.58/0.78  thf('0', plain, (~ (r1_tarski @ sk_C_3 @ (k7_relat_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(d3_relat_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( v1_relat_1 @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.78           ( ![C:$i,D:$i]:
% 0.58/0.78             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.58/0.78               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.58/0.78  thf('1', plain,
% 0.58/0.78      (![X10 : $i, X11 : $i]:
% 0.58/0.78         ((r2_hidden @ 
% 0.58/0.78           (k4_tarski @ (sk_C_1 @ X10 @ X11) @ (sk_D_1 @ X10 @ X11)) @ X11)
% 0.58/0.78          | (r1_tarski @ X11 @ X10)
% 0.58/0.78          | ~ (v1_relat_1 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.58/0.78  thf(d4_relat_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.58/0.78       ( ![C:$i]:
% 0.58/0.78         ( ( r2_hidden @ C @ B ) <=>
% 0.58/0.78           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.58/0.78  thf('2', plain,
% 0.58/0.78      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.78         (~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17)
% 0.58/0.78          | (r2_hidden @ X15 @ X18)
% 0.58/0.78          | ((X18) != (k1_relat_1 @ X17)))),
% 0.58/0.78      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.58/0.78  thf('3', plain,
% 0.58/0.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.78         ((r2_hidden @ X15 @ (k1_relat_1 @ X17))
% 0.58/0.78          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17))),
% 0.58/0.78      inference('simplify', [status(thm)], ['2'])).
% 0.58/0.78  thf('4', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ X0)
% 0.58/0.78          | (r1_tarski @ X0 @ X1)
% 0.58/0.78          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['1', '3'])).
% 0.58/0.78  thf('5', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(d3_tarski, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.78  thf('6', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.78          | (r2_hidden @ X0 @ X2)
% 0.58/0.78          | ~ (r1_tarski @ X1 @ X2))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.78  thf('7', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.78  thf('8', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r1_tarski @ sk_C_3 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ sk_C_3)
% 0.58/0.78          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['4', '7'])).
% 0.58/0.78  thf('9', plain, ((v1_relat_1 @ sk_C_3)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('10', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r1_tarski @ sk_C_3 @ X0)
% 0.58/0.78          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.78  thf('11', plain,
% 0.58/0.78      (![X10 : $i, X11 : $i]:
% 0.58/0.78         ((r2_hidden @ 
% 0.58/0.78           (k4_tarski @ (sk_C_1 @ X10 @ X11) @ (sk_D_1 @ X10 @ X11)) @ X11)
% 0.58/0.78          | (r1_tarski @ X11 @ X10)
% 0.58/0.78          | ~ (v1_relat_1 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.58/0.78  thf('12', plain, ((r1_tarski @ sk_C_3 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('13', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.78          | (r2_hidden @ X0 @ X2)
% 0.58/0.78          | ~ (r1_tarski @ X1 @ X2))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.78  thf('14', plain,
% 0.58/0.78      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.58/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.78  thf('15', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ sk_C_3)
% 0.58/0.78          | (r1_tarski @ sk_C_3 @ X0)
% 0.58/0.78          | (r2_hidden @ 
% 0.58/0.78             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ (sk_D_1 @ X0 @ sk_C_3)) @ 
% 0.58/0.78             sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['11', '14'])).
% 0.58/0.78  thf('16', plain, ((v1_relat_1 @ sk_C_3)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('17', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r1_tarski @ sk_C_3 @ X0)
% 0.58/0.78          | (r2_hidden @ 
% 0.58/0.78             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ (sk_D_1 @ X0 @ sk_C_3)) @ 
% 0.58/0.78             sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['15', '16'])).
% 0.58/0.78  thf(dt_k7_relat_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.58/0.78  thf('18', plain,
% 0.58/0.78      (![X22 : $i, X23 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ X22) | (v1_relat_1 @ (k7_relat_1 @ X22 @ X23)))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.58/0.78  thf(d11_relat_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( v1_relat_1 @ A ) =>
% 0.58/0.78       ( ![B:$i,C:$i]:
% 0.58/0.78         ( ( v1_relat_1 @ C ) =>
% 0.58/0.78           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 0.58/0.78             ( ![D:$i,E:$i]:
% 0.58/0.78               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.58/0.78                 ( ( r2_hidden @ D @ B ) & 
% 0.58/0.78                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.58/0.78  thf('19', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ X4)
% 0.58/0.78          | ((X4) != (k7_relat_1 @ X5 @ X6))
% 0.58/0.78          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ X4)
% 0.58/0.78          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X5)
% 0.58/0.78          | ~ (r2_hidden @ X7 @ X6)
% 0.58/0.78          | ~ (v1_relat_1 @ X5))),
% 0.58/0.78      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.58/0.78  thf('20', plain,
% 0.58/0.78      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ X5)
% 0.58/0.78          | ~ (r2_hidden @ X7 @ X6)
% 0.58/0.78          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X5)
% 0.58/0.78          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ (k7_relat_1 @ X5 @ X6))
% 0.58/0.78          | ~ (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['19'])).
% 0.58/0.78  thf('21', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ X1)
% 0.58/0.78          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.58/0.78          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.58/0.78          | ~ (r2_hidden @ X3 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X1))),
% 0.58/0.78      inference('sup-', [status(thm)], ['18', '20'])).
% 0.58/0.78  thf('22', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X3 @ X0)
% 0.58/0.78          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.58/0.78          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.58/0.78          | ~ (v1_relat_1 @ X1))),
% 0.58/0.78      inference('simplify', [status(thm)], ['21'])).
% 0.58/0.78  thf('23', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((r1_tarski @ sk_C_3 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ sk_B)
% 0.58/0.78          | (r2_hidden @ 
% 0.58/0.78             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ (sk_D_1 @ X0 @ sk_C_3)) @ 
% 0.58/0.78             (k7_relat_1 @ sk_B @ X1))
% 0.58/0.78          | ~ (r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ X1))),
% 0.58/0.78      inference('sup-', [status(thm)], ['17', '22'])).
% 0.58/0.78  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('25', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((r1_tarski @ sk_C_3 @ X0)
% 0.58/0.78          | (r2_hidden @ 
% 0.58/0.78             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ (sk_D_1 @ X0 @ sk_C_3)) @ 
% 0.58/0.78             (k7_relat_1 @ sk_B @ X1))
% 0.58/0.78          | ~ (r2_hidden @ (sk_C_1 @ X0 @ sk_C_3) @ X1))),
% 0.58/0.78      inference('demod', [status(thm)], ['23', '24'])).
% 0.58/0.78  thf('26', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r1_tarski @ sk_C_3 @ X0)
% 0.58/0.78          | (r2_hidden @ 
% 0.58/0.78             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ (sk_D_1 @ X0 @ sk_C_3)) @ 
% 0.58/0.78             (k7_relat_1 @ sk_B @ sk_A))
% 0.58/0.78          | (r1_tarski @ sk_C_3 @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['10', '25'])).
% 0.58/0.78  thf('27', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((r2_hidden @ 
% 0.58/0.78           (k4_tarski @ (sk_C_1 @ X0 @ sk_C_3) @ (sk_D_1 @ X0 @ sk_C_3)) @ 
% 0.58/0.78           (k7_relat_1 @ sk_B @ sk_A))
% 0.58/0.78          | (r1_tarski @ sk_C_3 @ X0))),
% 0.58/0.78      inference('simplify', [status(thm)], ['26'])).
% 0.58/0.78  thf('28', plain,
% 0.58/0.78      (![X10 : $i, X11 : $i]:
% 0.58/0.78         (~ (r2_hidden @ 
% 0.58/0.78             (k4_tarski @ (sk_C_1 @ X10 @ X11) @ (sk_D_1 @ X10 @ X11)) @ X10)
% 0.58/0.78          | (r1_tarski @ X11 @ X10)
% 0.58/0.78          | ~ (v1_relat_1 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.58/0.78  thf('29', plain,
% 0.58/0.78      (((r1_tarski @ sk_C_3 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.58/0.78        | ~ (v1_relat_1 @ sk_C_3)
% 0.58/0.78        | (r1_tarski @ sk_C_3 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['27', '28'])).
% 0.58/0.78  thf('30', plain, ((v1_relat_1 @ sk_C_3)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('31', plain,
% 0.58/0.78      (((r1_tarski @ sk_C_3 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.58/0.78        | (r1_tarski @ sk_C_3 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['29', '30'])).
% 0.58/0.78  thf('32', plain, ((r1_tarski @ sk_C_3 @ (k7_relat_1 @ sk_B @ sk_A))),
% 0.58/0.78      inference('simplify', [status(thm)], ['31'])).
% 0.58/0.78  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.58/0.78  
% 0.58/0.78  % SZS output end Refutation
% 0.58/0.78  
% 0.58/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
