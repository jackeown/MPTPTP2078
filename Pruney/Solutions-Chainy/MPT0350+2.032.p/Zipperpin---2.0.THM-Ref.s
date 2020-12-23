%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ILk5GNqPXv

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 106 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  490 ( 776 expanded)
%              Number of equality atoms :   44 (  75 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k4_subset_1 @ X30 @ X29 @ X31 )
        = ( k2_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k4_subset_1 @ X30 @ X29 @ X31 )
        = ( k3_tarski @ ( k2_tarski @ X29 @ X31 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('21',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r1_tarski @ X16 @ X14 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('23',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['21','23'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('28',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ k1_xboole_0 ) )
    = ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X5 @ k1_xboole_0 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('39',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','32','37','38'])).

thf('40',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['16','39'])).

thf('41',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['8','40'])).

thf('42',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('43',plain,(
    ! [X23: $i] :
      ( ( k2_subset_1 @ X23 )
      = X23 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ILk5GNqPXv
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 133 iterations in 0.035s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.48  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(t25_subset_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.48         ( k2_subset_1 @ A ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.48            ( k2_subset_1 @ A ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.21/0.48  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_k3_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X26 : $i, X27 : $i]:
% 0.21/0.48         ((m1_subset_1 @ (k3_subset_1 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))
% 0.21/0.48          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.48       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.21/0.48          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 0.21/0.48          | ((k4_subset_1 @ X30 @ X29 @ X31) = (k2_xboole_0 @ X29 @ X31)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.48  thf(l51_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.21/0.48          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 0.21/0.48          | ((k4_subset_1 @ X30 @ X29 @ X31)
% 0.21/0.48              = (k3_tarski @ (k2_tarski @ X29 @ X31))))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.21/0.48            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.48         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '7'])).
% 0.21/0.48  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d5_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X24 : $i, X25 : $i]:
% 0.21/0.48         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.21/0.48          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf(t39_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.21/0.48           = (k2_xboole_0 @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X6 @ (k4_xboole_0 @ X7 @ X6)))
% 0.21/0.48           = (k3_tarski @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.21/0.48         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['11', '15'])).
% 0.21/0.48  thf('17', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d2_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X20 : $i, X21 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X20 @ X21)
% 0.21/0.48          | (r2_hidden @ X20 @ X21)
% 0.21/0.48          | (v1_xboole_0 @ X21))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.48        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf(fc1_subset_1, axiom,
% 0.21/0.48    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.48  thf('20', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.48  thf('21', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf(d1_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X16 @ X15)
% 0.21/0.48          | (r1_tarski @ X16 @ X14)
% 0.21/0.48          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X14 : $i, X16 : $i]:
% 0.21/0.48         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.48  thf('24', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '23'])).
% 0.21/0.48  thf(l32_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X2 : $i, X4 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.48  thf('26', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X6 @ (k4_xboole_0 @ X7 @ X6)))
% 0.21/0.48           = (k3_tarski @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (((k3_tarski @ (k2_tarski @ sk_A @ k1_xboole_0))
% 0.21/0.48         = (k3_tarski @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 0.21/0.48           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 0.21/0.48           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.48  thf(t1_boole, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.48  thf('34', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X5 : $i]: ((k3_tarski @ (k2_tarski @ X5 @ k1_xboole_0)) = (X5))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['33', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 0.21/0.48           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.48  thf('39', plain, (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['28', '32', '37', '38'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '39'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['8', '40'])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.48         != (k2_subset_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.48  thf('43', plain, (![X23 : $i]: ((k2_subset_1 @ X23) = (X23))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['41', '44'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
