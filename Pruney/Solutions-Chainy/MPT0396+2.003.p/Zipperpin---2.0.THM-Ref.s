%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RKI4uepYrM

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  80 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  313 ( 625 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ ( k3_tarski @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ ( k3_tarski @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ X6 )
      | ~ ( r1_tarski @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_A )
    | ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r1_setfam_1 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_D @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ ( k3_tarski @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ ( sk_D @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( sk_D @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r1_setfam_1 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_setfam_1 @ sk_A @ X0 )
      | ( r1_tarski @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ X6 )
      | ~ ( r1_tarski @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('29',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RKI4uepYrM
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 100 iterations in 0.098s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.55  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(t18_setfam_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_setfam_1 @ A @ B ) =>
% 0.20/0.55       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( r1_setfam_1 @ A @ B ) =>
% 0.20/0.55          ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t18_setfam_1])).
% 0.20/0.55  thf('0', plain, (~ (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t94_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.20/0.55       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         ((r1_tarski @ (k3_tarski @ X5) @ X6)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         ((r1_tarski @ (k3_tarski @ X5) @ X6)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.55  thf(l49_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i]:
% 0.20/0.55         ((r1_tarski @ X3 @ (k3_tarski @ X4)) | ~ (r2_hidden @ X3 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.20/0.55          | (r1_tarski @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(t1_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.55       ( r1_tarski @ A @ C ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.55          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.55          | (r1_tarski @ X0 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.20/0.55          | (r1_tarski @ (sk_C @ X1 @ X0) @ X2)
% 0.20/0.55          | ~ (r1_tarski @ (k3_tarski @ X0) @ X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.20/0.55          | (r1_tarski @ (sk_C @ X2 @ X1) @ X0)
% 0.20/0.55          | (r1_tarski @ (k3_tarski @ X1) @ X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.55  thf('8', plain, (~ (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r1_tarski @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ X0)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         ((r1_tarski @ (k3_tarski @ X5) @ X6)
% 0.20/0.55          | ~ (r1_tarski @ (sk_C @ X6 @ X5) @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (((r2_hidden @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ sk_A)
% 0.20/0.55        | (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf('12', plain, (~ (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain, ((r2_hidden @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ sk_A)),
% 0.20/0.55      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('14', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d2_setfam_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.20/0.55       ( ![C:$i]:
% 0.20/0.55         ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.55              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_D @ X7 @ X8) @ X8)
% 0.20/0.55          | ~ (r2_hidden @ X7 @ X9)
% 0.20/0.55          | ~ (r1_setfam_1 @ X9 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ (sk_D @ X0 @ sk_B) @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((r2_hidden @ (sk_D @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ sk_B) @ sk_B)),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i]:
% 0.20/0.55         ((r1_tarski @ X3 @ (k3_tarski @ X4)) | ~ (r2_hidden @ X3 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      ((r1_tarski @ (sk_D @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ sk_B) @ 
% 0.20/0.55        (k3_tarski @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('20', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('21', plain, ((r2_hidden @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ sk_A)),
% 0.20/0.55      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((r1_tarski @ X7 @ (sk_D @ X7 @ X8))
% 0.20/0.55          | ~ (r2_hidden @ X7 @ X9)
% 0.20/0.55          | ~ (r1_setfam_1 @ X9 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_setfam_1 @ sk_A @ X0)
% 0.20/0.55          | (r1_tarski @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ 
% 0.20/0.55             (sk_D @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      ((r1_tarski @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ 
% 0.20/0.55        (sk_D @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.55          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.55          | (r1_tarski @ X0 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r1_tarski @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ X0)
% 0.20/0.55          | ~ (r1_tarski @ 
% 0.20/0.55               (sk_D @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ sk_B) @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      ((r1_tarski @ (sk_C @ (k3_tarski @ sk_B) @ sk_A) @ (k3_tarski @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['19', '26'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         ((r1_tarski @ (k3_tarski @ X5) @ X6)
% 0.20/0.55          | ~ (r1_tarski @ (sk_C @ X6 @ X5) @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.55  thf('29', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
