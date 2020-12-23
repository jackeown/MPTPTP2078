%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AqlHdZINvM

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:56 EST 2020

% Result     : Theorem 0.26s
% Output     : Refutation 0.26s
% Verified   : 
% Statistics : Number of formulae       :   50 (  63 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  305 ( 461 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k4_subset_1 @ X23 @ X22 @ X24 )
        = ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('15',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_tarski @ X9 @ X7 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('17',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['15','17'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X3
        = ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) ) )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('20',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','20'])).

thf('22',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('23',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('24',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('26',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AqlHdZINvM
% 0.16/0.39  % Computer   : n023.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 18:38:06 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.40  % Python version: Python 3.6.8
% 0.16/0.40  % Running in FO mode
% 0.26/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.26/0.54  % Solved by: fo/fo7.sh
% 0.26/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.26/0.54  % done 69 iterations in 0.033s
% 0.26/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.26/0.54  % SZS output start Refutation
% 0.26/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.26/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.26/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.26/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.26/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.26/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.26/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.26/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.26/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.26/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.26/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.26/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.26/0.54  thf(t25_subset_1, conjecture,
% 0.26/0.54    (![A:$i,B:$i]:
% 0.26/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.26/0.54       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.26/0.54         ( k2_subset_1 @ A ) ) ))).
% 0.26/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.26/0.54    (~( ![A:$i,B:$i]:
% 0.26/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.26/0.54          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.26/0.54            ( k2_subset_1 @ A ) ) ) )),
% 0.26/0.54    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.26/0.54  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.26/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.54  thf(dt_k3_subset_1, axiom,
% 0.26/0.54    (![A:$i,B:$i]:
% 0.26/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.26/0.54       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.26/0.54  thf('1', plain,
% 0.26/0.54      (![X19 : $i, X20 : $i]:
% 0.26/0.54         ((m1_subset_1 @ (k3_subset_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.26/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.26/0.54      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.26/0.54  thf('2', plain,
% 0.26/0.54      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.26/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.26/0.54  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.26/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.54  thf(d5_subset_1, axiom,
% 0.26/0.54    (![A:$i,B:$i]:
% 0.26/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.26/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.26/0.54  thf('4', plain,
% 0.26/0.54      (![X17 : $i, X18 : $i]:
% 0.26/0.54         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.26/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.26/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.26/0.54  thf('5', plain,
% 0.26/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.26/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.26/0.54  thf('6', plain,
% 0.26/0.54      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.26/0.54      inference('demod', [status(thm)], ['2', '5'])).
% 0.26/0.54  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.26/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.26/0.54    (![A:$i,B:$i,C:$i]:
% 0.26/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.26/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.26/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.26/0.54  thf('8', plain,
% 0.26/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.26/0.54         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.26/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 0.26/0.54          | ((k4_subset_1 @ X23 @ X22 @ X24) = (k2_xboole_0 @ X22 @ X24)))),
% 0.26/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.26/0.54  thf('9', plain,
% 0.26/0.54      (![X0 : $i]:
% 0.26/0.54         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.26/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.26/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.26/0.54  thf('10', plain,
% 0.26/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.26/0.54         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.26/0.54      inference('sup-', [status(thm)], ['6', '9'])).
% 0.26/0.54  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.26/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.54  thf(d2_subset_1, axiom,
% 0.26/0.54    (![A:$i,B:$i]:
% 0.26/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.26/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.26/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.26/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.26/0.54  thf('12', plain,
% 0.26/0.54      (![X13 : $i, X14 : $i]:
% 0.26/0.54         (~ (m1_subset_1 @ X13 @ X14)
% 0.26/0.54          | (r2_hidden @ X13 @ X14)
% 0.26/0.54          | (v1_xboole_0 @ X14))),
% 0.26/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.26/0.54  thf('13', plain,
% 0.26/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.26/0.54        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.26/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.26/0.54  thf(fc1_subset_1, axiom,
% 0.26/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.26/0.54  thf('14', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.26/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.26/0.54  thf('15', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.26/0.54      inference('clc', [status(thm)], ['13', '14'])).
% 0.26/0.54  thf(d1_zfmisc_1, axiom,
% 0.26/0.54    (![A:$i,B:$i]:
% 0.26/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.26/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.26/0.54  thf('16', plain,
% 0.26/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.26/0.54         (~ (r2_hidden @ X9 @ X8)
% 0.26/0.54          | (r1_tarski @ X9 @ X7)
% 0.26/0.54          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.26/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.26/0.54  thf('17', plain,
% 0.26/0.54      (![X7 : $i, X9 : $i]:
% 0.26/0.54         ((r1_tarski @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.26/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.26/0.54  thf('18', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.26/0.54      inference('sup-', [status(thm)], ['15', '17'])).
% 0.26/0.54  thf(t45_xboole_1, axiom,
% 0.26/0.54    (![A:$i,B:$i]:
% 0.26/0.54     ( ( r1_tarski @ A @ B ) =>
% 0.26/0.54       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.26/0.54  thf('19', plain,
% 0.26/0.54      (![X2 : $i, X3 : $i]:
% 0.26/0.54         (((X3) = (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2)))
% 0.26/0.54          | ~ (r1_tarski @ X2 @ X3))),
% 0.26/0.54      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.26/0.54  thf('20', plain,
% 0.26/0.54      (((sk_A) = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.26/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.26/0.54  thf('21', plain,
% 0.26/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.26/0.54      inference('demod', [status(thm)], ['10', '20'])).
% 0.26/0.54  thf('22', plain,
% 0.26/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.26/0.54         != (k2_subset_1 @ sk_A))),
% 0.26/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.26/0.54  thf('23', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 0.26/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.26/0.54  thf('24', plain,
% 0.26/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.26/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.26/0.54  thf('25', plain,
% 0.26/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.26/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.26/0.54  thf('26', plain,
% 0.26/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.26/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.26/0.54  thf('27', plain, ($false),
% 0.26/0.54      inference('simplify_reflect-', [status(thm)], ['21', '26'])).
% 0.26/0.54  
% 0.26/0.54  % SZS output end Refutation
% 0.26/0.54  
% 0.26/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
