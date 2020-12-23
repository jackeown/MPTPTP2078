%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sSTKtXHhAe

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 135 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  344 ( 987 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t25_finset_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
    <=> ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_finset_1 @ A )
          & ! [B: $i] :
              ( ( r2_hidden @ B @ A )
             => ( v1_finset_1 @ B ) ) )
      <=> ( v1_finset_1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_finset_1])).

thf('0',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(fc17_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( v1_finset_1 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( v1_finset_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc17_finset_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ ( k1_zfmisc_1 @ ( k3_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf(t13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ A ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_finset_1 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( v1_finset_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k3_tarski @ X0 ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X4 ) @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_finset_1 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( v1_finset_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('21',plain,
    ( ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v1_finset_1 @ sk_B_1 )
   <= ~ ( v1_finset_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,(
    ! [X11: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ X11 )
      | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('28',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(l22_finset_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
     => ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf('29',plain,(
    ! [X8: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X8 ) )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 )
      | ~ ( v1_finset_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('30',plain,
    ( ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) )
   <= ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('31',plain,
    ( ( ~ ( v1_finset_1 @ sk_A )
      | ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ ( sk_B @ sk_A ) ) )
   <= ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X8: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X8 ) )
      | ~ ( v1_finset_1 @ ( sk_B @ X8 ) )
      | ~ ( v1_finset_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('33',plain,
    ( ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ~ ( v1_finset_1 @ sk_A ) )
   <= ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( ( v1_finset_1 @ sk_A )
      & ! [X11: $i] :
          ( ( v1_finset_1 @ X11 )
          | ~ ( r2_hidden @ X11 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ~ ! [X11: $i] :
          ( ( v1_finset_1 @ X11 )
          | ~ ( r2_hidden @ X11 @ sk_A ) )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_finset_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['24','12','26','27','36'])).

thf('38',plain,(
    ~ ( v1_finset_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['23','37'])).

thf('39',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','39'])).

thf('41',plain,
    ( ! [X11: $i] :
        ( ( v1_finset_1 @ X11 )
        | ~ ( r2_hidden @ X11 @ sk_A ) )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('42',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','12','40','41','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sSTKtXHhAe
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 48 iterations in 0.020s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(t25_finset_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.48         ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) <=>
% 0.20/0.48       ( v1_finset_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.48            ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) <=>
% 0.20/0.48          ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t25_finset_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.48        | (r2_hidden @ sk_B_1 @ sk_A)
% 0.20/0.48        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.20/0.48       ~ ((v1_finset_1 @ (k3_tarski @ sk_A))) | ~ ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A)) | (v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((v1_finset_1 @ sk_A)) | ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf(fc17_finset_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X7 : $i]: ((v1_finset_1 @ (k1_zfmisc_1 @ X7)) | ~ (v1_finset_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc17_finset_1])).
% 0.20/0.48  thf(t100_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X3 : $i]: (r1_tarski @ X3 @ (k1_zfmisc_1 @ (k3_tarski @ X3)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.48  thf(t13_finset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( r1_tarski @ A @ B ) & ( v1_finset_1 @ B ) ) => ( v1_finset_1 @ A ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         ((v1_finset_1 @ X9) | ~ (r1_tarski @ X9 @ X10) | ~ (v1_finset_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_finset_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 0.20/0.48          | (v1_finset_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i]: (~ (v1_finset_1 @ (k3_tarski @ X0)) | (v1_finset_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.48  thf('11', plain, ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.48  thf(t56_setfam_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.48       ( r1_tarski @ C @ B ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k3_tarski @ X4) @ X5)
% 0.20/0.48          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.48          | (r1_tarski @ X6 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ (k3_tarski @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((r1_tarski @ sk_B_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         ((v1_finset_1 @ X9) | ~ (r1_tarski @ X9 @ X10) | ~ (v1_finset_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((~ (v1_finset_1 @ (k3_tarski @ sk_A)) | (v1_finset_1 @ sk_B_1)))
% 0.20/0.48         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.48        | ~ (v1_finset_1 @ sk_B_1)
% 0.20/0.48        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ sk_B_1)) <= (~ ((v1_finset_1 @ sk_B_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A))) | ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X11 : $i]:
% 0.20/0.48         ((v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.48          | (v1_finset_1 @ X11)
% 0.20/0.48          | ~ (r2_hidden @ X11 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A))) | 
% 0.20/0.48       (![X11 : $i]: ((v1_finset_1 @ X11) | ~ (r2_hidden @ X11 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (~ ((v1_finset_1 @ sk_B_1)) | ~ ((v1_finset_1 @ (k3_tarski @ sk_A))) | 
% 0.20/0.48       ~ ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('28', plain, (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf(l22_finset_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.48         ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) =>
% 0.20/0.48       ( v1_finset_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X8 : $i]:
% 0.20/0.48         ((v1_finset_1 @ (k3_tarski @ X8))
% 0.20/0.48          | (r2_hidden @ (sk_B @ X8) @ X8)
% 0.20/0.48          | ~ (v1_finset_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [l22_finset_1])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((![X11 : $i]: ((v1_finset_1 @ X11) | ~ (r2_hidden @ X11 @ sk_A)))
% 0.20/0.48         <= ((![X11 : $i]: ((v1_finset_1 @ X11) | ~ (r2_hidden @ X11 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['25'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((~ (v1_finset_1 @ sk_A)
% 0.20/0.48         | (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.48         | (v1_finset_1 @ (sk_B @ sk_A))))
% 0.20/0.48         <= ((![X11 : $i]: ((v1_finset_1 @ X11) | ~ (r2_hidden @ X11 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X8 : $i]:
% 0.20/0.48         ((v1_finset_1 @ (k3_tarski @ X8))
% 0.20/0.48          | ~ (v1_finset_1 @ (sk_B @ X8))
% 0.20/0.48          | ~ (v1_finset_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [l22_finset_1])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((((v1_finset_1 @ (k3_tarski @ sk_A)) | ~ (v1_finset_1 @ sk_A)))
% 0.20/0.48         <= ((![X11 : $i]: ((v1_finset_1 @ X11) | ~ (r2_hidden @ X11 @ sk_A))))),
% 0.20/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (((v1_finset_1 @ sk_A)) & 
% 0.20/0.48             (![X11 : $i]: ((v1_finset_1 @ X11) | ~ (r2_hidden @ X11 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (~ ((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (~ (![X11 : $i]: ((v1_finset_1 @ X11) | ~ (r2_hidden @ X11 @ sk_A))) | 
% 0.20/0.48       ((v1_finset_1 @ (k3_tarski @ sk_A))) | ~ ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, (~ ((v1_finset_1 @ sk_B_1))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)],
% 0.20/0.48                ['24', '12', '26', '27', '36'])).
% 0.20/0.48  thf('38', plain, (~ (v1_finset_1 @ sk_B_1)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['23', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((![X11 : $i]: ((v1_finset_1 @ X11) | ~ (r2_hidden @ X11 @ sk_A))) | 
% 0.20/0.48       ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['25'])).
% 0.20/0.48  thf('42', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)],
% 0.20/0.48                ['1', '3', '12', '40', '41', '36'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
