%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5bGEWnXkGl

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:02 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   50 (  71 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  295 ( 456 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t24_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r1_tarski @ C @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
       => ! [C: $i] :
            ( ( r2_hidden @ C @ B )
           => ( r1_tarski @ C @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_setfam_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X28 ) @ ( k3_tarski @ X29 ) )
      | ~ ( r1_setfam_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ ( k3_tarski @ X23 ) )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ sk_C_1 @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( r1_tarski @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_C_1 @ ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X26 ) @ X27 )
      | ( r2_hidden @ ( sk_C @ X27 @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ~ ( r1_tarski @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t24_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

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

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ ( k1_tarski @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ ( k3_tarski @ X23 ) )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( ( k3_tarski @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k3_tarski @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X26 ) @ X27 )
      | ~ ( r1_tarski @ ( sk_C @ X27 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( ( k3_tarski @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( ( k3_tarski @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['9','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5bGEWnXkGl
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:45:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.89/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.16  % Solved by: fo/fo7.sh
% 0.89/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.16  % done 1577 iterations in 0.716s
% 0.89/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.16  % SZS output start Refutation
% 0.89/1.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.89/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.16  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.89/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.16  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.89/1.16  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.89/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.16  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.89/1.16  thf(t24_setfam_1, conjecture,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.89/1.16       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ))).
% 0.89/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.16    (~( ![A:$i,B:$i]:
% 0.89/1.16        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.89/1.16          ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ) )),
% 0.89/1.16    inference('cnf.neg', [status(esa)], [t24_setfam_1])).
% 0.89/1.16  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ sk_A)),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf('1', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf(t18_setfam_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( r1_setfam_1 @ A @ B ) =>
% 0.89/1.16       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.89/1.16  thf('2', plain,
% 0.89/1.16      (![X28 : $i, X29 : $i]:
% 0.89/1.16         ((r1_tarski @ (k3_tarski @ X28) @ (k3_tarski @ X29))
% 0.89/1.16          | ~ (r1_setfam_1 @ X28 @ X29))),
% 0.89/1.16      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.89/1.16  thf('3', plain,
% 0.89/1.16      ((r1_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['1', '2'])).
% 0.89/1.16  thf('4', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf(l49_zfmisc_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.89/1.16  thf('5', plain,
% 0.89/1.16      (![X22 : $i, X23 : $i]:
% 0.89/1.16         ((r1_tarski @ X22 @ (k3_tarski @ X23)) | ~ (r2_hidden @ X22 @ X23))),
% 0.89/1.16      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.89/1.16  thf('6', plain, ((r1_tarski @ sk_C_1 @ (k3_tarski @ sk_B))),
% 0.89/1.16      inference('sup-', [status(thm)], ['4', '5'])).
% 0.89/1.16  thf(t1_xboole_1, axiom,
% 0.89/1.16    (![A:$i,B:$i,C:$i]:
% 0.89/1.16     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.89/1.16       ( r1_tarski @ A @ C ) ))).
% 0.89/1.16  thf('7', plain,
% 0.89/1.16      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.89/1.16         (~ (r1_tarski @ X8 @ X9)
% 0.89/1.16          | ~ (r1_tarski @ X9 @ X10)
% 0.89/1.16          | (r1_tarski @ X8 @ X10))),
% 0.89/1.16      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.89/1.16  thf('8', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ (k3_tarski @ sk_B) @ X0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['6', '7'])).
% 0.89/1.16  thf('9', plain, ((r1_tarski @ sk_C_1 @ (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['3', '8'])).
% 0.89/1.16  thf(t94_zfmisc_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.89/1.16       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.89/1.16  thf('10', plain,
% 0.89/1.16      (![X26 : $i, X27 : $i]:
% 0.89/1.16         ((r1_tarski @ (k3_tarski @ X26) @ X27)
% 0.89/1.16          | (r2_hidden @ (sk_C @ X27 @ X26) @ X26))),
% 0.89/1.16      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.89/1.16  thf(l1_zfmisc_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.89/1.16  thf('11', plain,
% 0.89/1.16      (![X19 : $i, X21 : $i]:
% 0.89/1.16         ((r1_tarski @ (k1_tarski @ X19) @ X21) | ~ (r2_hidden @ X19 @ X21))),
% 0.89/1.16      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.89/1.16  thf('12', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.89/1.16          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['10', '11'])).
% 0.89/1.16  thf(t24_zfmisc_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.89/1.16       ( ( A ) = ( B ) ) ))).
% 0.89/1.16  thf('13', plain,
% 0.89/1.16      (![X24 : $i, X25 : $i]:
% 0.89/1.16         (((X25) = (X24))
% 0.89/1.16          | ~ (r1_tarski @ (k1_tarski @ X25) @ (k1_tarski @ X24)))),
% 0.89/1.16      inference('cnf', [status(esa)], [t24_zfmisc_1])).
% 0.89/1.16  thf('14', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((r1_tarski @ (k3_tarski @ (k1_tarski @ X0)) @ X1)
% 0.89/1.16          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['12', '13'])).
% 0.89/1.16  thf(d10_xboole_0, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.16  thf('15', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.89/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.16  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.16      inference('simplify', [status(thm)], ['15'])).
% 0.89/1.16  thf('17', plain,
% 0.89/1.16      (![X19 : $i, X20 : $i]:
% 0.89/1.16         ((r2_hidden @ X19 @ X20) | ~ (r1_tarski @ (k1_tarski @ X19) @ X20))),
% 0.89/1.16      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.89/1.16  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['16', '17'])).
% 0.89/1.16  thf('19', plain,
% 0.89/1.16      (![X22 : $i, X23 : $i]:
% 0.89/1.16         ((r1_tarski @ X22 @ (k3_tarski @ X23)) | ~ (r2_hidden @ X22 @ X23))),
% 0.89/1.16      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.89/1.16  thf('20', plain,
% 0.89/1.16      (![X0 : $i]: (r1_tarski @ X0 @ (k3_tarski @ (k1_tarski @ X0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['18', '19'])).
% 0.89/1.16  thf('21', plain,
% 0.89/1.16      (![X0 : $i, X2 : $i]:
% 0.89/1.16         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.16  thf('22', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (r1_tarski @ (k3_tarski @ (k1_tarski @ X0)) @ X0)
% 0.89/1.16          | ((k3_tarski @ (k1_tarski @ X0)) = (X0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['20', '21'])).
% 0.89/1.16  thf('23', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (((sk_C @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.89/1.16          | ((k3_tarski @ (k1_tarski @ X0)) = (X0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['14', '22'])).
% 0.89/1.16  thf('24', plain,
% 0.89/1.16      (![X26 : $i, X27 : $i]:
% 0.89/1.16         ((r1_tarski @ (k3_tarski @ X26) @ X27)
% 0.89/1.16          | ~ (r1_tarski @ (sk_C @ X27 @ X26) @ X27))),
% 0.89/1.16      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.89/1.16  thf('25', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (r1_tarski @ X0 @ X0)
% 0.89/1.16          | ((k3_tarski @ (k1_tarski @ X0)) = (X0))
% 0.89/1.16          | (r1_tarski @ (k3_tarski @ (k1_tarski @ X0)) @ X0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['23', '24'])).
% 0.89/1.16  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.16      inference('simplify', [status(thm)], ['15'])).
% 0.89/1.16  thf('27', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (((k3_tarski @ (k1_tarski @ X0)) = (X0))
% 0.89/1.16          | (r1_tarski @ (k3_tarski @ (k1_tarski @ X0)) @ X0))),
% 0.89/1.16      inference('demod', [status(thm)], ['25', '26'])).
% 0.89/1.16  thf('28', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (r1_tarski @ (k3_tarski @ (k1_tarski @ X0)) @ X0)
% 0.89/1.16          | ((k3_tarski @ (k1_tarski @ X0)) = (X0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['20', '21'])).
% 0.89/1.16  thf('29', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.89/1.16      inference('clc', [status(thm)], ['27', '28'])).
% 0.89/1.16  thf('30', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.89/1.16      inference('demod', [status(thm)], ['9', '29'])).
% 0.89/1.16  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.89/1.16  
% 0.89/1.16  % SZS output end Refutation
% 0.89/1.16  
% 0.89/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
