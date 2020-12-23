%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6LMrMHIST4

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 145 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  489 (1055 expanded)
%              Number of equality atoms :   45 (  86 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( r1_tarski @ X23 @ ( k3_subset_1 @ X24 @ X25 ) )
      | ~ ( r1_tarski @ X25 @ ( k3_subset_1 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
      | ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('22',plain,(
    r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X18: $i] :
      ( ( k1_subset_1 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = ( k3_subset_1 @ X22 @ ( k1_subset_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('26',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = X19 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,(
    ! [X22: $i] :
      ( X22
      = ( k3_subset_1 @ X22 @ ( k1_subset_1 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('34',plain,(
    r1_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['40','47'])).

thf('49',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup+',[status(thm)],['10','48'])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6LMrMHIST4
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:40:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 478 iterations in 0.082s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(t40_subset_1, conjecture,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.22/0.55         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.55        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55          ( ( ( r1_tarski @ B @ C ) & 
% 0.22/0.55              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.22/0.55            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.22/0.55  thf('0', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t28_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (![X8 : $i, X9 : $i]:
% 0.22/0.55         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.55  thf('3', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(d5_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X20 : $i, X21 : $i]:
% 0.22/0.55         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.22/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.55  thf(t100_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X6 @ X7)
% 0.22/0.55           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.22/0.55         = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.55  thf(t92_xboole_1, axiom,
% 0.22/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.55  thf('9', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.55  thf('11', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('12', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t35_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ![C:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.22/0.55             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.22/0.55          | (r1_tarski @ X23 @ (k3_subset_1 @ X24 @ X25))
% 0.22/0.55          | ~ (r1_tarski @ X25 @ (k3_subset_1 @ X24 @ X23))
% 0.22/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.55          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.22/0.55          | (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.55          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.22/0.55          | (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ X0)))),
% 0.22/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (((r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ k1_xboole_0))
% 0.22/0.55        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['11', '16'])).
% 0.22/0.55  thf(t4_subset_1, axiom,
% 0.22/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X26 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X20 : $i, X21 : $i]:
% 0.22/0.55         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.22/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X26 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf('22', plain, ((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['17', '20', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.55  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.55  thf('24', plain, (![X18 : $i]: ((k1_subset_1 @ X18) = (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.55  thf(t22_subset_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (![X22 : $i]:
% 0.22/0.55         ((k2_subset_1 @ X22) = (k3_subset_1 @ X22 @ (k1_subset_1 @ X22)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.22/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.55  thf('26', plain, (![X19 : $i]: ((k2_subset_1 @ X19) = (X19))),
% 0.22/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (![X22 : $i]: ((X22) = (k3_subset_1 @ X22 @ (k1_subset_1 @ X22)))),
% 0.22/0.55      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.55  thf('28', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['24', '27'])).
% 0.22/0.55  thf('29', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['23', '28'])).
% 0.22/0.55  thf('30', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['22', '29'])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (![X8 : $i, X9 : $i]:
% 0.22/0.55         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.55  thf('32', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.55  thf(l97_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i]:
% 0.22/0.55         (r1_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ (k5_xboole_0 @ X4 @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.22/0.55  thf('34', plain, ((r1_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_C @ sk_A))),
% 0.22/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.22/0.55  thf('35', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t63_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.55       ( r1_xboole_0 @ A @ C ) ))).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.55         (~ (r1_tarski @ X11 @ X12)
% 0.22/0.55          | ~ (r1_xboole_0 @ X12 @ X13)
% 0.22/0.55          | (r1_xboole_0 @ X11 @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_C @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.55  thf('38', plain, ((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['34', '37'])).
% 0.22/0.55  thf(t83_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      (![X14 : $i, X15 : $i]:
% 0.22/0.55         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_A)) = (sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.55  thf('41', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X6 @ X7)
% 0.22/0.55           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.55  thf('44', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.22/0.55      inference('sup+', [status(thm)], ['41', '44'])).
% 0.22/0.55  thf(commutativity_k5_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.22/0.55      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_C @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['40', '47'])).
% 0.22/0.55  thf('49', plain, (((k1_xboole_0) = (sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['10', '48'])).
% 0.22/0.55  thf('50', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('51', plain, ($false),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
