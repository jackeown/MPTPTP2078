%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6QcuHxfE6L

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:51 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 138 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  455 ( 919 expanded)
%              Number of equality atoms :   19 (  50 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t19_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_relset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ( ( k3_relat_1 @ X20 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('11',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v5_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['13','18'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('35',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('49',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6QcuHxfE6L
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:20:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.96/1.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.96/1.13  % Solved by: fo/fo7.sh
% 0.96/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.96/1.13  % done 1483 iterations in 0.688s
% 0.96/1.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.96/1.13  % SZS output start Refutation
% 0.96/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.96/1.13  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.96/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.96/1.13  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.96/1.13  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.96/1.13  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.96/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.96/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.96/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.96/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.96/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.96/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.96/1.13  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.96/1.13  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.96/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.96/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.96/1.13  thf(t19_relset_1, conjecture,
% 0.96/1.13    (![A:$i,B:$i,C:$i]:
% 0.96/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.96/1.13       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.96/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.96/1.13    (~( ![A:$i,B:$i,C:$i]:
% 0.96/1.13        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.96/1.13          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.96/1.13    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.96/1.13  thf('0', plain,
% 0.96/1.13      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.96/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.13  thf(d6_relat_1, axiom,
% 0.96/1.13    (![A:$i]:
% 0.96/1.13     ( ( v1_relat_1 @ A ) =>
% 0.96/1.13       ( ( k3_relat_1 @ A ) =
% 0.96/1.13         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.96/1.13  thf('1', plain,
% 0.96/1.13      (![X20 : $i]:
% 0.96/1.13         (((k3_relat_1 @ X20)
% 0.96/1.13            = (k2_xboole_0 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20)))
% 0.96/1.13          | ~ (v1_relat_1 @ X20))),
% 0.96/1.13      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.96/1.13  thf(commutativity_k2_tarski, axiom,
% 0.96/1.13    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.96/1.13  thf('2', plain,
% 0.96/1.13      (![X10 : $i, X11 : $i]:
% 0.96/1.13         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.96/1.13      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.96/1.13  thf(l51_zfmisc_1, axiom,
% 0.96/1.13    (![A:$i,B:$i]:
% 0.96/1.13     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.96/1.13  thf('3', plain,
% 0.96/1.13      (![X12 : $i, X13 : $i]:
% 0.96/1.13         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 0.96/1.13      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.96/1.13  thf('4', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i]:
% 0.96/1.13         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.96/1.13      inference('sup+', [status(thm)], ['2', '3'])).
% 0.96/1.13  thf('5', plain,
% 0.96/1.13      (![X12 : $i, X13 : $i]:
% 0.96/1.13         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 0.96/1.13      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.96/1.13  thf('6', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.96/1.13      inference('sup+', [status(thm)], ['4', '5'])).
% 0.96/1.13  thf(t7_xboole_1, axiom,
% 0.96/1.13    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.96/1.13  thf('7', plain,
% 0.96/1.13      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.96/1.13      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.96/1.13  thf('8', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.96/1.13      inference('sup+', [status(thm)], ['6', '7'])).
% 0.96/1.13  thf('9', plain,
% 0.96/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.96/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.13  thf(cc2_relset_1, axiom,
% 0.96/1.13    (![A:$i,B:$i,C:$i]:
% 0.96/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.96/1.13       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.96/1.13  thf('10', plain,
% 0.96/1.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.96/1.13         ((v5_relat_1 @ X23 @ X25)
% 0.96/1.13          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.96/1.13      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.96/1.13  thf('11', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.96/1.13      inference('sup-', [status(thm)], ['9', '10'])).
% 0.96/1.13  thf(d19_relat_1, axiom,
% 0.96/1.13    (![A:$i,B:$i]:
% 0.96/1.13     ( ( v1_relat_1 @ B ) =>
% 0.96/1.13       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.96/1.13  thf('12', plain,
% 0.96/1.13      (![X18 : $i, X19 : $i]:
% 0.96/1.13         (~ (v5_relat_1 @ X18 @ X19)
% 0.96/1.13          | (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.96/1.13          | ~ (v1_relat_1 @ X18))),
% 0.96/1.13      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.96/1.13  thf('13', plain,
% 0.96/1.13      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.96/1.13      inference('sup-', [status(thm)], ['11', '12'])).
% 0.96/1.13  thf('14', plain,
% 0.96/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.96/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.13  thf(cc2_relat_1, axiom,
% 0.96/1.13    (![A:$i]:
% 0.96/1.13     ( ( v1_relat_1 @ A ) =>
% 0.96/1.13       ( ![B:$i]:
% 0.96/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.96/1.13  thf('15', plain,
% 0.96/1.13      (![X14 : $i, X15 : $i]:
% 0.96/1.13         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.96/1.13          | (v1_relat_1 @ X14)
% 0.96/1.13          | ~ (v1_relat_1 @ X15))),
% 0.96/1.13      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.96/1.13  thf('16', plain,
% 0.96/1.13      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.96/1.13      inference('sup-', [status(thm)], ['14', '15'])).
% 0.96/1.13  thf(fc6_relat_1, axiom,
% 0.96/1.13    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.96/1.13  thf('17', plain,
% 0.96/1.13      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.96/1.13      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.96/1.13  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.96/1.13      inference('demod', [status(thm)], ['16', '17'])).
% 0.96/1.13  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.96/1.13      inference('demod', [status(thm)], ['13', '18'])).
% 0.96/1.13  thf(t12_xboole_1, axiom,
% 0.96/1.13    (![A:$i,B:$i]:
% 0.96/1.13     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.96/1.13  thf('20', plain,
% 0.96/1.13      (![X3 : $i, X4 : $i]:
% 0.96/1.13         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.96/1.13      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.96/1.13  thf('21', plain, (((k2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B) = (sk_B))),
% 0.96/1.13      inference('sup-', [status(thm)], ['19', '20'])).
% 0.96/1.13  thf('22', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.96/1.13      inference('sup+', [status(thm)], ['4', '5'])).
% 0.96/1.13  thf('23', plain, (((k2_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)) = (sk_B))),
% 0.96/1.13      inference('demod', [status(thm)], ['21', '22'])).
% 0.96/1.13  thf('24', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.96/1.13      inference('sup+', [status(thm)], ['4', '5'])).
% 0.96/1.13  thf(t11_xboole_1, axiom,
% 0.96/1.13    (![A:$i,B:$i,C:$i]:
% 0.96/1.13     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.96/1.13  thf('25', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.13         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.96/1.13      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.96/1.13  thf('26', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.13         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 0.96/1.13      inference('sup-', [status(thm)], ['24', '25'])).
% 0.96/1.13  thf('27', plain,
% 0.96/1.13      (![X0 : $i]:
% 0.96/1.13         (~ (r1_tarski @ sk_B @ X0) | (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 0.96/1.13      inference('sup-', [status(thm)], ['23', '26'])).
% 0.96/1.13  thf('28', plain,
% 0.96/1.13      (![X0 : $i]:
% 0.96/1.13         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.96/1.13      inference('sup-', [status(thm)], ['8', '27'])).
% 0.96/1.13  thf('29', plain,
% 0.96/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.96/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.13  thf('30', plain,
% 0.96/1.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.96/1.13         ((v4_relat_1 @ X23 @ X24)
% 0.96/1.13          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.96/1.13      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.96/1.13  thf('31', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.96/1.13      inference('sup-', [status(thm)], ['29', '30'])).
% 0.96/1.13  thf(d18_relat_1, axiom,
% 0.96/1.13    (![A:$i,B:$i]:
% 0.96/1.13     ( ( v1_relat_1 @ B ) =>
% 0.96/1.13       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.96/1.13  thf('32', plain,
% 0.96/1.13      (![X16 : $i, X17 : $i]:
% 0.96/1.13         (~ (v4_relat_1 @ X16 @ X17)
% 0.96/1.13          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.96/1.13          | ~ (v1_relat_1 @ X16))),
% 0.96/1.13      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.96/1.13  thf('33', plain,
% 0.96/1.13      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.96/1.13      inference('sup-', [status(thm)], ['31', '32'])).
% 0.96/1.13  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.96/1.13      inference('demod', [status(thm)], ['16', '17'])).
% 0.96/1.13  thf('35', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.96/1.13      inference('demod', [status(thm)], ['33', '34'])).
% 0.96/1.13  thf('36', plain,
% 0.96/1.13      (![X3 : $i, X4 : $i]:
% 0.96/1.13         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.96/1.13      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.96/1.13  thf('37', plain, (((k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) = (sk_A))),
% 0.96/1.13      inference('sup-', [status(thm)], ['35', '36'])).
% 0.96/1.13  thf('38', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.96/1.13      inference('sup+', [status(thm)], ['4', '5'])).
% 0.96/1.13  thf('39', plain, (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 0.96/1.13      inference('demod', [status(thm)], ['37', '38'])).
% 0.96/1.13  thf('40', plain,
% 0.96/1.13      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.96/1.13      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.96/1.13  thf('41', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.13         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 0.96/1.13      inference('sup-', [status(thm)], ['24', '25'])).
% 0.96/1.13  thf('42', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.13         (r1_tarski @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.96/1.13      inference('sup-', [status(thm)], ['40', '41'])).
% 0.96/1.13  thf('43', plain,
% 0.96/1.13      (![X0 : $i]:
% 0.96/1.13         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 0.96/1.13      inference('sup+', [status(thm)], ['39', '42'])).
% 0.96/1.13  thf(t8_xboole_1, axiom,
% 0.96/1.13    (![A:$i,B:$i,C:$i]:
% 0.96/1.13     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.96/1.13       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.96/1.13  thf('44', plain,
% 0.96/1.13      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.96/1.13         (~ (r1_tarski @ X7 @ X8)
% 0.96/1.13          | ~ (r1_tarski @ X9 @ X8)
% 0.96/1.13          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.96/1.13      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.96/1.13  thf('45', plain,
% 0.96/1.13      (![X0 : $i, X1 : $i]:
% 0.96/1.13         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 0.96/1.13           (k2_xboole_0 @ sk_A @ X0))
% 0.96/1.13          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.96/1.13      inference('sup-', [status(thm)], ['43', '44'])).
% 0.96/1.13  thf('46', plain,
% 0.96/1.13      ((r1_tarski @ 
% 0.96/1.13        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 0.96/1.13        (k2_xboole_0 @ sk_A @ sk_B))),
% 0.96/1.13      inference('sup-', [status(thm)], ['28', '45'])).
% 0.96/1.13  thf('47', plain,
% 0.96/1.13      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.96/1.13        | ~ (v1_relat_1 @ sk_C))),
% 0.96/1.13      inference('sup+', [status(thm)], ['1', '46'])).
% 0.96/1.13  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.96/1.13      inference('demod', [status(thm)], ['16', '17'])).
% 0.96/1.13  thf('49', plain,
% 0.96/1.13      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.96/1.13      inference('demod', [status(thm)], ['47', '48'])).
% 0.96/1.13  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.96/1.13  
% 0.96/1.13  % SZS output end Refutation
% 0.96/1.13  
% 0.96/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
