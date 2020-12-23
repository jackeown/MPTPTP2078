%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vc5vyUqxu4

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:47 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  441 ( 695 expanded)
%              Number of equality atoms :   10 (  26 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X8 ) ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X8 ) ) ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( r1_tarski @ ( k2_relat_1 @ X44 ) @ ( k2_relat_1 @ X43 ) )
      | ~ ( r1_tarski @ X44 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X38: $i,X40: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( r1_tarski @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_relat_1 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','14'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('17',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) @ X1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( r1_tarski @ ( k2_relat_1 @ X44 ) @ ( k2_relat_1 @ X43 ) )
      | ~ ( r1_tarski @ X44 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) @ X1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X38: $i,X40: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( r1_tarski @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_relat_1 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','25'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('28',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['36','37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vc5vyUqxu4
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:38:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 300 iterations in 0.132s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.59  thf(idempotence_k2_xboole_0, axiom,
% 0.42/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.42/0.59  thf('0', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.42/0.59      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.42/0.59  thf(t31_xboole_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( r1_tarski @
% 0.42/0.59       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.42/0.59       ( k2_xboole_0 @ B @ C ) ))).
% 0.42/0.59  thf('1', plain,
% 0.42/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.59         (r1_tarski @ 
% 0.42/0.59          (k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X8)) @ 
% 0.42/0.59          (k2_xboole_0 @ X7 @ X8))),
% 0.42/0.59      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.42/0.59  thf(t12_setfam_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.42/0.59  thf('2', plain,
% 0.42/0.59      (![X36 : $i, X37 : $i]:
% 0.42/0.59         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.42/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.59  thf('3', plain,
% 0.42/0.59      (![X36 : $i, X37 : $i]:
% 0.42/0.59         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.42/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.59  thf('4', plain,
% 0.42/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.59         (r1_tarski @ 
% 0.42/0.59          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7)) @ 
% 0.42/0.59           (k1_setfam_1 @ (k2_tarski @ X6 @ X8))) @ 
% 0.42/0.59          (k2_xboole_0 @ X7 @ X8))),
% 0.42/0.59      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.42/0.59  thf('5', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.42/0.59          (k2_xboole_0 @ X0 @ X0))),
% 0.42/0.59      inference('sup+', [status(thm)], ['0', '4'])).
% 0.42/0.59  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.42/0.59      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.42/0.59  thf('7', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.42/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.42/0.59  thf(t25_relat_1, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( v1_relat_1 @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( v1_relat_1 @ B ) =>
% 0.42/0.59           ( ( r1_tarski @ A @ B ) =>
% 0.42/0.59             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.42/0.59               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.42/0.59  thf('8', plain,
% 0.42/0.59      (![X43 : $i, X44 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ X43)
% 0.42/0.59          | (r1_tarski @ (k2_relat_1 @ X44) @ (k2_relat_1 @ X43))
% 0.42/0.59          | ~ (r1_tarski @ X44 @ X43)
% 0.42/0.59          | ~ (v1_relat_1 @ X44))),
% 0.42/0.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.42/0.59  thf('9', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.42/0.59          | (r1_tarski @ 
% 0.42/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.42/0.59             (k2_relat_1 @ X0))
% 0.42/0.59          | ~ (v1_relat_1 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.59  thf('10', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.42/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.42/0.59  thf(t3_subset, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.59  thf('11', plain,
% 0.42/0.59      (![X38 : $i, X40 : $i]:
% 0.42/0.59         ((m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X40)) | ~ (r1_tarski @ X38 @ X40))),
% 0.42/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.59  thf('12', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.42/0.59          (k1_zfmisc_1 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.59  thf(cc2_relat_1, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( v1_relat_1 @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.42/0.59  thf('13', plain,
% 0.42/0.59      (![X41 : $i, X42 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.42/0.59          | (v1_relat_1 @ X41)
% 0.42/0.59          | ~ (v1_relat_1 @ X42))),
% 0.42/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.59  thf('14', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ X0)
% 0.42/0.59          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.59  thf('15', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ X0)
% 0.42/0.59          | (r1_tarski @ 
% 0.42/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.42/0.59             (k2_relat_1 @ X0)))),
% 0.42/0.59      inference('clc', [status(thm)], ['9', '14'])).
% 0.42/0.59  thf(t17_xboole_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.42/0.59  thf('16', plain,
% 0.42/0.59      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.42/0.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.42/0.59  thf('17', plain,
% 0.42/0.59      (![X36 : $i, X37 : $i]:
% 0.42/0.59         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.42/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.59  thf('18', plain,
% 0.42/0.59      (![X1 : $i, X2 : $i]:
% 0.42/0.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2)) @ X1)),
% 0.42/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('19', plain,
% 0.42/0.59      (![X43 : $i, X44 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ X43)
% 0.42/0.59          | (r1_tarski @ (k2_relat_1 @ X44) @ (k2_relat_1 @ X43))
% 0.42/0.59          | ~ (r1_tarski @ X44 @ X43)
% 0.42/0.59          | ~ (v1_relat_1 @ X44))),
% 0.42/0.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.42/0.59  thf('20', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.42/0.59          | (r1_tarski @ 
% 0.42/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.42/0.59             (k2_relat_1 @ X0))
% 0.42/0.59          | ~ (v1_relat_1 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.59  thf('21', plain,
% 0.42/0.59      (![X1 : $i, X2 : $i]:
% 0.42/0.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2)) @ X1)),
% 0.42/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      (![X38 : $i, X40 : $i]:
% 0.42/0.59         ((m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X40)) | ~ (r1_tarski @ X38 @ X40))),
% 0.42/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.59  thf('23', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.42/0.59          (k1_zfmisc_1 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.59  thf('24', plain,
% 0.42/0.59      (![X41 : $i, X42 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.42/0.59          | (v1_relat_1 @ X41)
% 0.42/0.59          | ~ (v1_relat_1 @ X42))),
% 0.42/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.59  thf('25', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ X0)
% 0.42/0.59          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.59  thf('26', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ X0)
% 0.42/0.59          | (r1_tarski @ 
% 0.42/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.42/0.59             (k2_relat_1 @ X0)))),
% 0.42/0.59      inference('clc', [status(thm)], ['20', '25'])).
% 0.42/0.59  thf(t19_xboole_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.42/0.59       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.42/0.59  thf('27', plain,
% 0.42/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.59         (~ (r1_tarski @ X3 @ X4)
% 0.42/0.59          | ~ (r1_tarski @ X3 @ X5)
% 0.42/0.59          | (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.42/0.59      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.42/0.59  thf('28', plain,
% 0.42/0.59      (![X36 : $i, X37 : $i]:
% 0.42/0.59         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.42/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.59  thf('29', plain,
% 0.42/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.59         (~ (r1_tarski @ X3 @ X4)
% 0.42/0.59          | ~ (r1_tarski @ X3 @ X5)
% 0.42/0.59          | (r1_tarski @ X3 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 0.42/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.42/0.59  thf('30', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ X0)
% 0.42/0.59          | (r1_tarski @ 
% 0.42/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.42/0.59             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X2)))
% 0.42/0.59          | ~ (r1_tarski @ 
% 0.42/0.59               (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.42/0.59      inference('sup-', [status(thm)], ['26', '29'])).
% 0.42/0.59  thf('31', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ X0)
% 0.42/0.59          | (r1_tarski @ 
% 0.42/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.42/0.59             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.42/0.59          | ~ (v1_relat_1 @ X1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['15', '30'])).
% 0.42/0.59  thf(t27_relat_1, conjecture,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( v1_relat_1 @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( v1_relat_1 @ B ) =>
% 0.42/0.59           ( r1_tarski @
% 0.42/0.59             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.42/0.59             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i]:
% 0.42/0.59        ( ( v1_relat_1 @ A ) =>
% 0.42/0.59          ( ![B:$i]:
% 0.42/0.59            ( ( v1_relat_1 @ B ) =>
% 0.42/0.59              ( r1_tarski @
% 0.42/0.59                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.42/0.59                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.42/0.59          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('33', plain,
% 0.42/0.59      (![X36 : $i, X37 : $i]:
% 0.42/0.59         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.42/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.59  thf('34', plain,
% 0.42/0.59      (![X36 : $i, X37 : $i]:
% 0.42/0.59         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.42/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.59  thf('35', plain,
% 0.42/0.59      (~ (r1_tarski @ 
% 0.42/0.59          (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.42/0.59          (k1_setfam_1 @ 
% 0.42/0.59           (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.42/0.59      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.42/0.59  thf('36', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['31', '35'])).
% 0.42/0.59  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('39', plain, ($false),
% 0.42/0.59      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.42/0.59  
% 0.42/0.59  % SZS output end Refutation
% 0.42/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
