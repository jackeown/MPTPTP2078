%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SVumbdSyUX

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 (  98 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  382 ( 641 expanded)
%              Number of equality atoms :   33 (  49 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ ( k3_tarski @ X18 ) )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('13',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('14',plain,(
    ! [X19: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('15',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('19',plain,(
    r1_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 )
      | ( r1_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup+',[status(thm)],['6','37'])).

thf('39',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SVumbdSyUX
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 103 iterations in 0.037s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(t40_subset_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.20/0.48         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48          ( ( ( r1_tarski @ B @ C ) & 
% 0.20/0.48              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.20/0.48            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.20/0.48  thf('0', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t28_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t100_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X6 @ X7)
% 0.20/0.48           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.20/0.48         = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(t92_xboole_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('5', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d2_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X20 @ X21)
% 0.20/0.48          | (r2_hidden @ X20 @ X21)
% 0.20/0.48          | (v1_xboole_0 @ X21))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.48        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(fc1_subset_1, axiom,
% 0.20/0.48    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('10', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.48  thf('11', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf(l49_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i]:
% 0.20/0.48         ((r1_tarski @ X17 @ (k3_tarski @ X18)) | ~ (r2_hidden @ X17 @ X18))),
% 0.20/0.48      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.48  thf('13', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf(t99_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.48  thf('14', plain, (![X19 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X19)) = (X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.48  thf('15', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.48  thf('17', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf(l97_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (r1_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ (k5_xboole_0 @ X4 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.20/0.48  thf('19', plain, ((r1_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_C @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X6 @ X7)
% 0.20/0.48           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.48           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.48      inference('sup+', [status(thm)], ['20', '23'])).
% 0.20/0.48  thf(commutativity_k5_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, ((r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '26'])).
% 0.20/0.48  thf('28', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t63_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.48       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X10 @ X11)
% 0.20/0.48          | ~ (r1_xboole_0 @ X11 @ X12)
% 0.20/0.48          | (r1_xboole_0 @ X10 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_C @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.48  thf(t83_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d5_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X23 : $i, X24 : $i]:
% 0.20/0.48         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 0.20/0.48          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '36'])).
% 0.20/0.48  thf('38', plain, (((k1_xboole_0) = (sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['6', '37'])).
% 0.20/0.48  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('40', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
