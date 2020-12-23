%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5mD2HgFk4Q

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:20 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  281 ( 513 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t88_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_tarski @ E @ F )
        & ( r1_tarski @ G @ H ) )
     => ( r1_tarski @ ( k4_zfmisc_1 @ A @ C @ E @ G ) @ ( k4_zfmisc_1 @ B @ D @ F @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D )
          & ( r1_tarski @ E @ F )
          & ( r1_tarski @ G @ H ) )
       => ( r1_tarski @ ( k4_zfmisc_1 @ A @ C @ E @ G ) @ ( k4_zfmisc_1 @ B @ D @ F @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_mcart_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ sk_G ) @ ( k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_G @ sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tarski @ sk_E @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t119_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t119_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t119_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ X1 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_C @ X1 ) @ ( k3_zfmisc_1 @ sk_B @ sk_D @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_zfmisc_1 @ sk_B @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t119_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_C @ sk_E ) @ X1 ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_B @ sk_D @ sk_F ) @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ X1 ) @ ( k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ sk_G ) @ ( k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ sk_H ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5mD2HgFk4Q
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:23:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 191 iterations in 0.224s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.68  thf(sk_G_type, type, sk_G: $i).
% 0.46/0.68  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.68  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.68  thf(sk_H_type, type, sk_H: $i).
% 0.46/0.68  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.46/0.68  thf(sk_F_type, type, sk_F: $i).
% 0.46/0.68  thf(t88_mcart_1, conjecture,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.46/0.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.46/0.68         ( r1_tarski @ E @ F ) & ( r1_tarski @ G @ H ) ) =>
% 0.46/0.68       ( r1_tarski @
% 0.46/0.68         ( k4_zfmisc_1 @ A @ C @ E @ G ) @ ( k4_zfmisc_1 @ B @ D @ F @ H ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.46/0.68        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.46/0.68            ( r1_tarski @ E @ F ) & ( r1_tarski @ G @ H ) ) =>
% 0.46/0.68          ( r1_tarski @
% 0.46/0.68            ( k4_zfmisc_1 @ A @ C @ E @ G ) @ ( k4_zfmisc_1 @ B @ D @ F @ H ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t88_mcart_1])).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      (~ (r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ sk_G) @ 
% 0.46/0.68          (k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ sk_H))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('1', plain, ((r1_tarski @ sk_G @ sk_H)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('2', plain, ((r1_tarski @ sk_E @ sk_F)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('3', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t119_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.46/0.68       ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.68          | ~ (r1_tarski @ X2 @ X3)
% 0.46/0.68          | (r1_tarski @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t119_zfmisc_1])).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0))
% 0.46/0.68          | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['3', '6'])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.68          | ~ (r1_tarski @ X2 @ X3)
% 0.46/0.68          | (r1_tarski @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t119_zfmisc_1])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_tarski @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ X1) @ 
% 0.46/0.68           (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D) @ X0))
% 0.46/0.68          | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.68  thf(d3_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.46/0.68       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.68         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.46/0.68           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.46/0.68      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.68         ((k3_zfmisc_1 @ X4 @ X5 @ X6)
% 0.46/0.68           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5) @ X6))),
% 0.46/0.68      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_C @ X1) @ 
% 0.46/0.68           (k3_zfmisc_1 @ sk_B @ sk_D @ X0))
% 0.46/0.68          | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      ((r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_C @ sk_E) @ 
% 0.46/0.68        (k3_zfmisc_1 @ sk_B @ sk_D @ sk_F))),
% 0.46/0.68      inference('sup-', [status(thm)], ['2', '12'])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.68          | ~ (r1_tarski @ X2 @ X3)
% 0.46/0.68          | (r1_tarski @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t119_zfmisc_1])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_tarski @ 
% 0.46/0.68           (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_C @ sk_E) @ X1) @ 
% 0.46/0.68           (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_B @ sk_D @ sk_F) @ X0))
% 0.46/0.68          | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.68  thf(d4_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.46/0.68       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.68         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.46/0.68           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.68         ((k4_zfmisc_1 @ X7 @ X8 @ X9 @ X10)
% 0.46/0.68           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X7 @ X8 @ X9) @ X10))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ X1) @ 
% 0.46/0.68           (k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ X0))
% 0.46/0.68          | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      ((r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ sk_G) @ 
% 0.46/0.68        (k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ sk_H))),
% 0.46/0.68      inference('sup-', [status(thm)], ['1', '18'])).
% 0.46/0.68  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
