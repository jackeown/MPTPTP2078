%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FdJXdv5nsv

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  44 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  178 ( 292 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t215_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t215_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( r1_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ X9 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X9 ) @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 )
      | ( r1_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('13',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FdJXdv5nsv
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:37:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 20 iterations in 0.013s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(t215_relat_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.47             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v1_relat_1 @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( v1_relat_1 @ B ) =>
% 0.21/0.47              ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.47                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t215_relat_1])).
% 0.21/0.47  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t127_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.21/0.47       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6) @ (k2_zfmisc_1 @ X7 @ X8))
% 0.21/0.47          | ~ (r1_xboole_0 @ X6 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ sk_A)) @ 
% 0.21/0.47          (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(t21_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( r1_tarski @
% 0.21/0.47         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X9 : $i]:
% 0.21/0.47         ((r1_tarski @ X9 @ 
% 0.21/0.47           (k2_zfmisc_1 @ (k1_relat_1 @ X9) @ (k2_relat_1 @ X9)))
% 0.21/0.47          | ~ (v1_relat_1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.21/0.47  thf(t63_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.47       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X2 @ X3)
% 0.21/0.47          | ~ (r1_xboole_0 @ X3 @ X4)
% 0.21/0.47          | (r1_xboole_0 @ X2 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | (r1_xboole_0 @ X0 @ X1)
% 0.21/0.47          | ~ (r1_xboole_0 @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ sk_A @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.21/0.47          | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.47  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (r1_xboole_0 @ sk_A @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_B)) @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | (r1_xboole_0 @ X0 @ X1)
% 0.21/0.47          | ~ (r1_xboole_0 @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('13', plain, (((r1_xboole_0 @ sk_B @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.47  thf('17', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
