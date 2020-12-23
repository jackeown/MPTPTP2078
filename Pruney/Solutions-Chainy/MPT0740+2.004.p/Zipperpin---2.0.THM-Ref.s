%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PsWsUT5OXw

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  75 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   19
%              Number of atoms          :  369 ( 496 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X18 ) )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('1',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X18 ) )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( v1_ordinal1 @ X11 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r1_tarski @ X9 @ X10 )
      | ~ ( v1_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( v1_ordinal1 @ X11 )
      | ~ ( r1_tarski @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t22_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r1_tarski @ A @ B )
                  & ( r2_hidden @ B @ C ) )
               => ( r2_hidden @ A @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v3_ordinal1 @ X15 )
      | ~ ( v1_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t22_ordinal1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('25',plain,(
    ! [X8: $i] :
      ( ( v1_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v3_ordinal1 @ X16 )
      | ~ ( v3_ordinal1 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v3_ordinal1 @ X16 )
      | ~ ( v3_ordinal1 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','32'])).

thf(t30_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_ordinal1])).

thf('34',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PsWsUT5OXw
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 94 iterations in 0.057s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.51  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.20/0.51  thf(t29_ordinal1, axiom,
% 0.20/0.51    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X18 : $i]:
% 0.20/0.51         ((v3_ordinal1 @ (k1_ordinal1 @ X18)) | ~ (v3_ordinal1 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X18 : $i]:
% 0.20/0.51         ((v3_ordinal1 @ (k1_ordinal1 @ X18)) | ~ (v3_ordinal1 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.51  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.51  thf('2', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_ordinal1 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.51  thf(d2_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_ordinal1 @ A ) <=>
% 0.20/0.51       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X11 : $i]: ((v1_ordinal1 @ X11) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.20/0.51  thf(t94_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.20/0.51       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((r1_tarski @ (k3_tarski @ X6) @ X7)
% 0.20/0.51          | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.51          | (r1_tarski @ X9 @ X10)
% 0.20/0.51          | ~ (v1_ordinal1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.20/0.51          | ~ (v1_ordinal1 @ X0)
% 0.20/0.51          | (r1_tarski @ (sk_C_1 @ X1 @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((r1_tarski @ (k3_tarski @ X6) @ X7)
% 0.20/0.51          | ~ (r1_tarski @ (sk_C_1 @ X7 @ X6) @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_ordinal1 @ X0)
% 0.20/0.51          | (r1_tarski @ (k3_tarski @ X0) @ X0)
% 0.20/0.51          | (r1_tarski @ (k3_tarski @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X2)
% 0.20/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_ordinal1 @ X0)
% 0.20/0.51          | (r2_hidden @ X1 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X1 @ (k3_tarski @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_ordinal1 @ (k3_tarski @ X0))
% 0.20/0.51          | (r2_hidden @ (sk_B @ (k3_tarski @ X0)) @ X0)
% 0.20/0.51          | ~ (v1_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '11'])).
% 0.20/0.51  thf(l49_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         ((r1_tarski @ X4 @ (k3_tarski @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_ordinal1 @ X0)
% 0.20/0.51          | (v1_ordinal1 @ (k3_tarski @ X0))
% 0.20/0.51          | (r1_tarski @ (sk_B @ (k3_tarski @ X0)) @ (k3_tarski @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X11 : $i]: ((v1_ordinal1 @ X11) | ~ (r1_tarski @ (sk_B @ X11) @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i]: ((v1_ordinal1 @ (k3_tarski @ X0)) | ~ (v1_ordinal1 @ X0))),
% 0.20/0.51      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.51  thf(t22_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( v3_ordinal1 @ C ) =>
% 0.20/0.51               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.20/0.51                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X13)
% 0.20/0.51          | ~ (r1_tarski @ X14 @ X13)
% 0.20/0.51          | ~ (r2_hidden @ X13 @ X15)
% 0.20/0.51          | (r2_hidden @ X14 @ X15)
% 0.20/0.51          | ~ (v3_ordinal1 @ X15)
% 0.20/0.51          | ~ (v1_ordinal1 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [t22_ordinal1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_ordinal1 @ X0)
% 0.20/0.51          | ~ (v1_ordinal1 @ (k3_tarski @ X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v1_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v1_ordinal1 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v1_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_ordinal1 @ X0)
% 0.20/0.51          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.51  thf(cc1_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.20/0.51  thf('25', plain, (![X8 : $i]: ((v1_ordinal1 @ X8) | ~ (v3_ordinal1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0)))),
% 0.20/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf(t23_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         ((v3_ordinal1 @ X16)
% 0.20/0.51          | ~ (v3_ordinal1 @ X17)
% 0.20/0.51          | ~ (r2_hidden @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.20/0.51          | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_ordinal1 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         ((v3_ordinal1 @ X16)
% 0.20/0.51          | ~ (v3_ordinal1 @ X17)
% 0.20/0.51          | ~ (r2_hidden @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v3_ordinal1 @ (k1_ordinal1 @ X0)) | (v3_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v3_ordinal1 @ (k3_tarski @ X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.20/0.51      inference('clc', [status(thm)], ['28', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '32'])).
% 0.20/0.51  thf(t30_ordinal1, conjecture,
% 0.20/0.51    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t30_ordinal1])).
% 0.20/0.51  thf('34', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain, ($false), inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
