%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h3z8eVCN2t

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:03 EST 2020

% Result     : Theorem 10.92s
% Output     : Refutation 10.92s
% Verified   : 
% Statistics : Number of formulae       :   60 (  92 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  409 ( 680 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( r1_tarski @ ( k2_xboole_0 @ X17 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k3_relat_1 @ X26 ) @ ( k3_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','20'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k3_relat_1 @ X26 ) @ ( k3_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('26',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['24','29'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ( r1_tarski @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h3z8eVCN2t
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:40:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 10.92/11.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.92/11.12  % Solved by: fo/fo7.sh
% 10.92/11.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.92/11.12  % done 14171 iterations in 10.658s
% 10.92/11.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.92/11.12  % SZS output start Refutation
% 10.92/11.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 10.92/11.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 10.92/11.12  thf(sk_A_type, type, sk_A: $i).
% 10.92/11.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.92/11.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.92/11.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.92/11.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.92/11.12  thf(sk_B_type, type, sk_B: $i).
% 10.92/11.12  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 10.92/11.12  thf(d10_xboole_0, axiom,
% 10.92/11.12    (![A:$i,B:$i]:
% 10.92/11.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.92/11.12  thf('0', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 10.92/11.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.92/11.12  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 10.92/11.12      inference('simplify', [status(thm)], ['0'])).
% 10.92/11.12  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 10.92/11.12      inference('simplify', [status(thm)], ['0'])).
% 10.92/11.12  thf(t8_xboole_1, axiom,
% 10.92/11.12    (![A:$i,B:$i,C:$i]:
% 10.92/11.12     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 10.92/11.12       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 10.92/11.12  thf('3', plain,
% 10.92/11.12      (![X17 : $i, X18 : $i, X19 : $i]:
% 10.92/11.12         (~ (r1_tarski @ X17 @ X18)
% 10.92/11.12          | ~ (r1_tarski @ X19 @ X18)
% 10.92/11.12          | (r1_tarski @ (k2_xboole_0 @ X17 @ X19) @ X18))),
% 10.92/11.12      inference('cnf', [status(esa)], [t8_xboole_1])).
% 10.92/11.12  thf('4', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 10.92/11.12      inference('sup-', [status(thm)], ['2', '3'])).
% 10.92/11.12  thf('5', plain, (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ X0)),
% 10.92/11.12      inference('sup-', [status(thm)], ['1', '4'])).
% 10.92/11.12  thf(t7_xboole_1, axiom,
% 10.92/11.12    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 10.92/11.12  thf('6', plain,
% 10.92/11.12      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 10.92/11.12      inference('cnf', [status(esa)], [t7_xboole_1])).
% 10.92/11.12  thf('7', plain,
% 10.92/11.12      (![X0 : $i, X2 : $i]:
% 10.92/11.12         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 10.92/11.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.92/11.12  thf('8', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 10.92/11.12          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 10.92/11.12      inference('sup-', [status(thm)], ['6', '7'])).
% 10.92/11.12  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 10.92/11.12      inference('sup-', [status(thm)], ['5', '8'])).
% 10.92/11.12  thf(t31_xboole_1, axiom,
% 10.92/11.12    (![A:$i,B:$i,C:$i]:
% 10.92/11.12     ( r1_tarski @
% 10.92/11.12       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 10.92/11.12       ( k2_xboole_0 @ B @ C ) ))).
% 10.92/11.12  thf('10', plain,
% 10.92/11.12      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.92/11.12         (r1_tarski @ 
% 10.92/11.12          (k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k3_xboole_0 @ X12 @ X14)) @ 
% 10.92/11.12          (k2_xboole_0 @ X13 @ X14))),
% 10.92/11.12      inference('cnf', [status(esa)], [t31_xboole_1])).
% 10.92/11.12  thf(t11_xboole_1, axiom,
% 10.92/11.12    (![A:$i,B:$i,C:$i]:
% 10.92/11.12     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 10.92/11.12  thf('11', plain,
% 10.92/11.12      (![X3 : $i, X4 : $i, X5 : $i]:
% 10.92/11.12         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 10.92/11.12      inference('cnf', [status(esa)], [t11_xboole_1])).
% 10.92/11.12  thf('12', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.92/11.12         (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 10.92/11.12      inference('sup-', [status(thm)], ['10', '11'])).
% 10.92/11.12  thf('13', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 10.92/11.12      inference('sup+', [status(thm)], ['9', '12'])).
% 10.92/11.12  thf(t31_relat_1, axiom,
% 10.92/11.12    (![A:$i]:
% 10.92/11.12     ( ( v1_relat_1 @ A ) =>
% 10.92/11.12       ( ![B:$i]:
% 10.92/11.12         ( ( v1_relat_1 @ B ) =>
% 10.92/11.12           ( ( r1_tarski @ A @ B ) =>
% 10.92/11.12             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 10.92/11.12  thf('14', plain,
% 10.92/11.12      (![X25 : $i, X26 : $i]:
% 10.92/11.12         (~ (v1_relat_1 @ X25)
% 10.92/11.12          | (r1_tarski @ (k3_relat_1 @ X26) @ (k3_relat_1 @ X25))
% 10.92/11.12          | ~ (r1_tarski @ X26 @ X25)
% 10.92/11.12          | ~ (v1_relat_1 @ X26))),
% 10.92/11.12      inference('cnf', [status(esa)], [t31_relat_1])).
% 10.92/11.12  thf('15', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 10.92/11.12          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 10.92/11.12             (k3_relat_1 @ X0))
% 10.92/11.12          | ~ (v1_relat_1 @ X0))),
% 10.92/11.12      inference('sup-', [status(thm)], ['13', '14'])).
% 10.92/11.12  thf('16', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 10.92/11.12      inference('sup+', [status(thm)], ['9', '12'])).
% 10.92/11.12  thf(t3_subset, axiom,
% 10.92/11.12    (![A:$i,B:$i]:
% 10.92/11.12     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.92/11.12  thf('17', plain,
% 10.92/11.12      (![X20 : $i, X22 : $i]:
% 10.92/11.12         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 10.92/11.12      inference('cnf', [status(esa)], [t3_subset])).
% 10.92/11.12  thf('18', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 10.92/11.12      inference('sup-', [status(thm)], ['16', '17'])).
% 10.92/11.12  thf(cc2_relat_1, axiom,
% 10.92/11.12    (![A:$i]:
% 10.92/11.12     ( ( v1_relat_1 @ A ) =>
% 10.92/11.12       ( ![B:$i]:
% 10.92/11.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 10.92/11.12  thf('19', plain,
% 10.92/11.12      (![X23 : $i, X24 : $i]:
% 10.92/11.12         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 10.92/11.12          | (v1_relat_1 @ X23)
% 10.92/11.12          | ~ (v1_relat_1 @ X24))),
% 10.92/11.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.92/11.12  thf('20', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 10.92/11.12      inference('sup-', [status(thm)], ['18', '19'])).
% 10.92/11.12  thf('21', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         (~ (v1_relat_1 @ X0)
% 10.92/11.12          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 10.92/11.12             (k3_relat_1 @ X0)))),
% 10.92/11.12      inference('clc', [status(thm)], ['15', '20'])).
% 10.92/11.12  thf(t17_xboole_1, axiom,
% 10.92/11.12    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 10.92/11.12  thf('22', plain,
% 10.92/11.12      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 10.92/11.12      inference('cnf', [status(esa)], [t17_xboole_1])).
% 10.92/11.12  thf('23', plain,
% 10.92/11.12      (![X25 : $i, X26 : $i]:
% 10.92/11.12         (~ (v1_relat_1 @ X25)
% 10.92/11.12          | (r1_tarski @ (k3_relat_1 @ X26) @ (k3_relat_1 @ X25))
% 10.92/11.12          | ~ (r1_tarski @ X26 @ X25)
% 10.92/11.12          | ~ (v1_relat_1 @ X26))),
% 10.92/11.12      inference('cnf', [status(esa)], [t31_relat_1])).
% 10.92/11.12  thf('24', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 10.92/11.12          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 10.92/11.12             (k3_relat_1 @ X0))
% 10.92/11.12          | ~ (v1_relat_1 @ X0))),
% 10.92/11.12      inference('sup-', [status(thm)], ['22', '23'])).
% 10.92/11.12  thf('25', plain,
% 10.92/11.12      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 10.92/11.12      inference('cnf', [status(esa)], [t17_xboole_1])).
% 10.92/11.12  thf('26', plain,
% 10.92/11.12      (![X20 : $i, X22 : $i]:
% 10.92/11.12         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 10.92/11.12      inference('cnf', [status(esa)], [t3_subset])).
% 10.92/11.12  thf('27', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 10.92/11.12      inference('sup-', [status(thm)], ['25', '26'])).
% 10.92/11.12  thf('28', plain,
% 10.92/11.12      (![X23 : $i, X24 : $i]:
% 10.92/11.12         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 10.92/11.12          | (v1_relat_1 @ X23)
% 10.92/11.12          | ~ (v1_relat_1 @ X24))),
% 10.92/11.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.92/11.12  thf('29', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 10.92/11.12      inference('sup-', [status(thm)], ['27', '28'])).
% 10.92/11.12  thf('30', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         (~ (v1_relat_1 @ X0)
% 10.92/11.12          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 10.92/11.12             (k3_relat_1 @ X0)))),
% 10.92/11.12      inference('clc', [status(thm)], ['24', '29'])).
% 10.92/11.12  thf(t19_xboole_1, axiom,
% 10.92/11.12    (![A:$i,B:$i,C:$i]:
% 10.92/11.12     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 10.92/11.12       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 10.92/11.12  thf('31', plain,
% 10.92/11.12      (![X8 : $i, X9 : $i, X10 : $i]:
% 10.92/11.12         (~ (r1_tarski @ X8 @ X9)
% 10.92/11.12          | ~ (r1_tarski @ X8 @ X10)
% 10.92/11.12          | (r1_tarski @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 10.92/11.12      inference('cnf', [status(esa)], [t19_xboole_1])).
% 10.92/11.12  thf('32', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.92/11.12         (~ (v1_relat_1 @ X0)
% 10.92/11.12          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 10.92/11.12             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 10.92/11.12          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 10.92/11.12      inference('sup-', [status(thm)], ['30', '31'])).
% 10.92/11.12  thf('33', plain,
% 10.92/11.12      (![X0 : $i, X1 : $i]:
% 10.92/11.12         (~ (v1_relat_1 @ X0)
% 10.92/11.12          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 10.92/11.12             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 10.92/11.12          | ~ (v1_relat_1 @ X1))),
% 10.92/11.12      inference('sup-', [status(thm)], ['21', '32'])).
% 10.92/11.12  thf(t34_relat_1, conjecture,
% 10.92/11.12    (![A:$i]:
% 10.92/11.12     ( ( v1_relat_1 @ A ) =>
% 10.92/11.12       ( ![B:$i]:
% 10.92/11.12         ( ( v1_relat_1 @ B ) =>
% 10.92/11.12           ( r1_tarski @
% 10.92/11.12             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 10.92/11.12             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 10.92/11.12  thf(zf_stmt_0, negated_conjecture,
% 10.92/11.12    (~( ![A:$i]:
% 10.92/11.12        ( ( v1_relat_1 @ A ) =>
% 10.92/11.12          ( ![B:$i]:
% 10.92/11.12            ( ( v1_relat_1 @ B ) =>
% 10.92/11.12              ( r1_tarski @
% 10.92/11.12                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 10.92/11.12                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 10.92/11.12    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 10.92/11.12  thf('34', plain,
% 10.92/11.12      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 10.92/11.12          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 10.92/11.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.92/11.12  thf('35', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 10.92/11.12      inference('sup-', [status(thm)], ['33', '34'])).
% 10.92/11.12  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 10.92/11.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.92/11.12  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 10.92/11.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.92/11.12  thf('38', plain, ($false),
% 10.92/11.12      inference('demod', [status(thm)], ['35', '36', '37'])).
% 10.92/11.12  
% 10.92/11.12  % SZS output end Refutation
% 10.92/11.12  
% 10.92/11.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
