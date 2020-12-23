%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6UVfP8MAX0

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  75 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   19
%              Number of atoms          :  372 ( 499 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X17 ) )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('1',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X17 ) )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( v1_ordinal1 @ X10 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
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

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X2 ) @ ( k3_tarski @ X3 ) )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X4 ) @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X10: $i] :
      ( ( v1_ordinal1 @ X10 )
      | ~ ( r1_tarski @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 )
      | ~ ( v1_ordinal1 @ X13 ) ) ),
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
    ! [X7: $i] :
      ( ( v1_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X7 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6UVfP8MAX0
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 64 iterations in 0.046s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.50  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.50  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.50  thf(t29_ordinal1, axiom,
% 0.21/0.50    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X17 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X17 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.21/0.50  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.21/0.50  thf('2', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_ordinal1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.21/0.50  thf(d2_ordinal1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_ordinal1 @ A ) <=>
% 0.21/0.50       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X10 : $i]: ((v1_ordinal1 @ X10) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.50  thf(t94_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.21/0.50       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X8 @ X9)
% 0.21/0.50          | (r1_tarski @ X8 @ X9)
% 0.21/0.50          | ~ (v1_ordinal1 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.21/0.50          | ~ (v1_ordinal1 @ X0)
% 0.21/0.50          | (r1_tarski @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.21/0.50          | ~ (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_ordinal1 @ X0)
% 0.21/0.50          | (r1_tarski @ (k3_tarski @ X0) @ X0)
% 0.21/0.50          | (r1_tarski @ (k3_tarski @ X0) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  thf(t95_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.50       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ X2) @ (k3_tarski @ X3))
% 0.21/0.50          | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_ordinal1 @ X0)
% 0.21/0.50          | (r1_tarski @ (k3_tarski @ (k3_tarski @ X0)) @ (k3_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf(t56_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.21/0.50       ( r1_tarski @ C @ B ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k3_tarski @ X4) @ X5)
% 0.21/0.50          | ~ (r2_hidden @ X6 @ X4)
% 0.21/0.50          | (r1_tarski @ X6 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_ordinal1 @ X0)
% 0.21/0.50          | (r1_tarski @ X1 @ (k3_tarski @ X0))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ (k3_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_ordinal1 @ (k3_tarski @ X0))
% 0.21/0.50          | (r1_tarski @ (sk_B @ (k3_tarski @ X0)) @ (k3_tarski @ X0))
% 0.21/0.50          | ~ (v1_ordinal1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X10 : $i]: ((v1_ordinal1 @ X10) | ~ (r1_tarski @ (sk_B @ X10) @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_ordinal1 @ X0) | (v1_ordinal1 @ (k3_tarski @ X0)))),
% 0.21/0.50      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]: ((r1_tarski @ (k3_tarski @ X0) @ X0) | ~ (v1_ordinal1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  thf(t22_ordinal1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( v3_ordinal1 @ C ) =>
% 0.21/0.50               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.21/0.50                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X12)
% 0.21/0.50          | ~ (r1_tarski @ X13 @ X12)
% 0.21/0.50          | ~ (r2_hidden @ X12 @ X14)
% 0.21/0.50          | (r2_hidden @ X13 @ X14)
% 0.21/0.50          | ~ (v3_ordinal1 @ X14)
% 0.21/0.50          | ~ (v1_ordinal1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t22_ordinal1])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_ordinal1 @ X0)
% 0.21/0.50          | ~ (v1_ordinal1 @ (k3_tarski @ X0))
% 0.21/0.50          | ~ (v3_ordinal1 @ X1)
% 0.21/0.50          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.21/0.50          | ~ (v3_ordinal1 @ X1)
% 0.21/0.50          | ~ (v1_ordinal1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X1)
% 0.21/0.50          | (r2_hidden @ (k3_tarski @ X0) @ X1)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | ~ (v1_ordinal1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.21/0.50          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | ~ (v1_ordinal1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_ordinal1 @ X0)
% 0.21/0.50          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0))
% 0.21/0.50          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.50  thf(cc1_ordinal1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.50  thf('25', plain, (![X7 : $i]: ((v1_ordinal1 @ X7) | ~ (v3_ordinal1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (r2_hidden @ (k3_tarski @ X0) @ (k1_ordinal1 @ X0)))),
% 0.21/0.50      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf(t23_ordinal1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ X15)
% 0.21/0.50          | ~ (v3_ordinal1 @ X16)
% 0.21/0.50          | ~ (r2_hidden @ X15 @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X0)
% 0.21/0.50          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.21/0.50          | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_ordinal1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ X15)
% 0.21/0.50          | ~ (v3_ordinal1 @ X16)
% 0.21/0.50          | ~ (r2_hidden @ X15 @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v3_ordinal1 @ (k1_ordinal1 @ X0)) | (v3_ordinal1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ (k3_tarski @ X0))
% 0.21/0.50          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.21/0.50      inference('clc', [status(thm)], ['28', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '32'])).
% 0.21/0.50  thf(t30_ordinal1, conjecture,
% 0.21/0.50    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t30_ordinal1])).
% 0.21/0.50  thf('34', plain, (~ (v3_ordinal1 @ (k3_tarski @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain, ($false), inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
