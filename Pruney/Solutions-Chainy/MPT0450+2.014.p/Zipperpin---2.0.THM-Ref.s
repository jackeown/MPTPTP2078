%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kuf0OySX7l

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:03 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   52 (  68 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  340 ( 494 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('1',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k3_relat_1 @ X26 ) @ ( k3_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','12'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k3_relat_1 @ X26 ) @ ( k3_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('18',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','21'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

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

thf('26',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kuf0OySX7l
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:52:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 367 iterations in 0.199s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.44/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.44/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.66  thf(d2_tarski, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.44/0.66       ( ![D:$i]:
% 0.44/0.66         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.44/0.66  thf('0', plain,
% 0.44/0.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.66         (((X6) != (X5))
% 0.44/0.66          | (r2_hidden @ X6 @ X7)
% 0.44/0.66          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.44/0.66      inference('cnf', [status(esa)], [d2_tarski])).
% 0.44/0.66  thf('1', plain,
% 0.44/0.66      (![X5 : $i, X8 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X8 @ X5))),
% 0.44/0.66      inference('simplify', [status(thm)], ['0'])).
% 0.44/0.66  thf(t4_setfam_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      (![X21 : $i, X22 : $i]:
% 0.44/0.66         ((r1_tarski @ (k1_setfam_1 @ X21) @ X22) | ~ (r2_hidden @ X22 @ X21))),
% 0.44/0.66      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.44/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.66  thf(t12_setfam_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.66  thf('4', plain,
% 0.44/0.66      (![X16 : $i, X17 : $i]:
% 0.44/0.66         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 0.44/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.44/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.44/0.66  thf(t31_relat_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ A ) =>
% 0.44/0.66       ( ![B:$i]:
% 0.44/0.66         ( ( v1_relat_1 @ B ) =>
% 0.44/0.66           ( ( r1_tarski @ A @ B ) =>
% 0.44/0.66             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.44/0.66  thf('6', plain,
% 0.44/0.66      (![X25 : $i, X26 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ X25)
% 0.44/0.66          | (r1_tarski @ (k3_relat_1 @ X26) @ (k3_relat_1 @ X25))
% 0.44/0.66          | ~ (r1_tarski @ X26 @ X25)
% 0.44/0.66          | ~ (v1_relat_1 @ X26))),
% 0.44/0.66      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.44/0.66  thf('7', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.44/0.66          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.44/0.66             (k3_relat_1 @ X0))
% 0.44/0.66          | ~ (v1_relat_1 @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.44/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.44/0.66  thf(t3_subset, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.66  thf('9', plain,
% 0.44/0.66      (![X18 : $i, X20 : $i]:
% 0.44/0.66         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.44/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.66  thf('10', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.66  thf(cc2_relat_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ A ) =>
% 0.44/0.66       ( ![B:$i]:
% 0.44/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.44/0.66  thf('11', plain,
% 0.44/0.66      (![X23 : $i, X24 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.44/0.66          | (v1_relat_1 @ X23)
% 0.44/0.66          | ~ (v1_relat_1 @ X24))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.44/0.66  thf('12', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.66  thf('13', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ X0)
% 0.44/0.66          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.44/0.66             (k3_relat_1 @ X0)))),
% 0.44/0.66      inference('clc', [status(thm)], ['7', '12'])).
% 0.44/0.66  thf(t17_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.66  thf('14', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.44/0.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.44/0.66  thf('15', plain,
% 0.44/0.66      (![X25 : $i, X26 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ X25)
% 0.44/0.66          | (r1_tarski @ (k3_relat_1 @ X26) @ (k3_relat_1 @ X25))
% 0.44/0.66          | ~ (r1_tarski @ X26 @ X25)
% 0.44/0.66          | ~ (v1_relat_1 @ X26))),
% 0.44/0.66      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.44/0.66  thf('16', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.44/0.66          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.44/0.66             (k3_relat_1 @ X0))
% 0.44/0.66          | ~ (v1_relat_1 @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.66  thf('17', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.44/0.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.44/0.66  thf('18', plain,
% 0.44/0.66      (![X18 : $i, X20 : $i]:
% 0.44/0.66         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.44/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.66  thf('19', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.66  thf('20', plain,
% 0.44/0.66      (![X23 : $i, X24 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.44/0.66          | (v1_relat_1 @ X23)
% 0.44/0.66          | ~ (v1_relat_1 @ X24))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.44/0.66  thf('21', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.66  thf('22', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ X0)
% 0.44/0.66          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.44/0.66             (k3_relat_1 @ X0)))),
% 0.44/0.66      inference('clc', [status(thm)], ['16', '21'])).
% 0.44/0.66  thf(t19_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.44/0.66       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.66  thf('23', plain,
% 0.44/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.66         (~ (r1_tarski @ X2 @ X3)
% 0.44/0.66          | ~ (r1_tarski @ X2 @ X4)
% 0.44/0.66          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.44/0.66  thf('24', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ X0)
% 0.44/0.66          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.44/0.66             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 0.44/0.66          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.44/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.66  thf('25', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ X0)
% 0.44/0.66          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.44/0.66             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 0.44/0.66          | ~ (v1_relat_1 @ X1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['13', '24'])).
% 0.44/0.66  thf(t34_relat_1, conjecture,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ A ) =>
% 0.44/0.66       ( ![B:$i]:
% 0.44/0.66         ( ( v1_relat_1 @ B ) =>
% 0.44/0.66           ( r1_tarski @
% 0.44/0.66             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.44/0.66             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i]:
% 0.44/0.66        ( ( v1_relat_1 @ A ) =>
% 0.44/0.66          ( ![B:$i]:
% 0.44/0.66            ( ( v1_relat_1 @ B ) =>
% 0.44/0.66              ( r1_tarski @
% 0.44/0.66                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.44/0.66                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.44/0.66  thf('26', plain,
% 0.44/0.66      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.44/0.66          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('27', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.44/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.66  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('30', plain, ($false),
% 0.44/0.66      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
