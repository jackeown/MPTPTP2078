%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0INydQsyCh

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:50 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 143 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  508 ( 959 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X33: $i] :
      ( ( ( k3_relat_1 @ X33 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v5_relat_1 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v5_relat_1 @ X31 @ X32 )
      | ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X34: $i,X35: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['15','20'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v4_relat_1 @ X29 @ X30 )
      | ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('31',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ( r1_tarski @ ( k2_xboole_0 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) ) @ sk_A ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ( r1_tarski @ ( k2_xboole_0 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('51',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('54',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0INydQsyCh
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.82/3.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.82/3.04  % Solved by: fo/fo7.sh
% 2.82/3.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.82/3.04  % done 4377 iterations in 2.583s
% 2.82/3.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.82/3.04  % SZS output start Refutation
% 2.82/3.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.82/3.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.82/3.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.82/3.04  thf(sk_A_type, type, sk_A: $i).
% 2.82/3.04  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.82/3.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.82/3.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.82/3.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.82/3.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.82/3.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.82/3.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.82/3.04  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.82/3.04  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.82/3.04  thf(sk_B_type, type, sk_B: $i).
% 2.82/3.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.82/3.04  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.82/3.04  thf(sk_C_type, type, sk_C: $i).
% 2.82/3.04  thf(t19_relset_1, conjecture,
% 2.82/3.04    (![A:$i,B:$i,C:$i]:
% 2.82/3.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.04       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.82/3.04  thf(zf_stmt_0, negated_conjecture,
% 2.82/3.04    (~( ![A:$i,B:$i,C:$i]:
% 2.82/3.04        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.04          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 2.82/3.04    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 2.82/3.04  thf('0', plain,
% 2.82/3.04      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 2.82/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.04  thf(d6_relat_1, axiom,
% 2.82/3.04    (![A:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ A ) =>
% 2.82/3.04       ( ( k3_relat_1 @ A ) =
% 2.82/3.04         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.82/3.04  thf('1', plain,
% 2.82/3.04      (![X33 : $i]:
% 2.82/3.04         (((k3_relat_1 @ X33)
% 2.82/3.04            = (k2_xboole_0 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33)))
% 2.82/3.04          | ~ (v1_relat_1 @ X33))),
% 2.82/3.04      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.82/3.04  thf(commutativity_k2_tarski, axiom,
% 2.82/3.04    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.82/3.04  thf('2', plain,
% 2.82/3.04      (![X14 : $i, X15 : $i]:
% 2.82/3.04         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 2.82/3.04      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.82/3.04  thf(l51_zfmisc_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.82/3.04  thf('3', plain,
% 2.82/3.04      (![X18 : $i, X19 : $i]:
% 2.82/3.04         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 2.82/3.04      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.82/3.04  thf('4', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 2.82/3.04      inference('sup+', [status(thm)], ['2', '3'])).
% 2.82/3.04  thf('5', plain,
% 2.82/3.04      (![X18 : $i, X19 : $i]:
% 2.82/3.04         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 2.82/3.04      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.82/3.04  thf('6', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.82/3.04      inference('sup+', [status(thm)], ['4', '5'])).
% 2.82/3.04  thf(t36_xboole_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.82/3.04  thf('7', plain,
% 2.82/3.04      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 2.82/3.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.82/3.04  thf(t44_xboole_1, axiom,
% 2.82/3.04    (![A:$i,B:$i,C:$i]:
% 2.82/3.04     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 2.82/3.04       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.82/3.04  thf('8', plain,
% 2.82/3.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.82/3.04         ((r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 2.82/3.04          | ~ (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 2.82/3.04      inference('cnf', [status(esa)], [t44_xboole_1])).
% 2.82/3.04  thf('9', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.82/3.04      inference('sup-', [status(thm)], ['7', '8'])).
% 2.82/3.04  thf('10', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 2.82/3.04      inference('sup+', [status(thm)], ['6', '9'])).
% 2.82/3.04  thf('11', plain,
% 2.82/3.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.04  thf(cc2_relset_1, axiom,
% 2.82/3.04    (![A:$i,B:$i,C:$i]:
% 2.82/3.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.04       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.82/3.04  thf('12', plain,
% 2.82/3.04      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.82/3.04         ((v5_relat_1 @ X36 @ X38)
% 2.82/3.04          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 2.82/3.04      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.82/3.04  thf('13', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 2.82/3.04      inference('sup-', [status(thm)], ['11', '12'])).
% 2.82/3.04  thf(d19_relat_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ B ) =>
% 2.82/3.04       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.82/3.04  thf('14', plain,
% 2.82/3.04      (![X31 : $i, X32 : $i]:
% 2.82/3.04         (~ (v5_relat_1 @ X31 @ X32)
% 2.82/3.04          | (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 2.82/3.04          | ~ (v1_relat_1 @ X31))),
% 2.82/3.04      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.82/3.04  thf('15', plain,
% 2.82/3.04      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 2.82/3.04      inference('sup-', [status(thm)], ['13', '14'])).
% 2.82/3.04  thf('16', plain,
% 2.82/3.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.04  thf(cc2_relat_1, axiom,
% 2.82/3.04    (![A:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ A ) =>
% 2.82/3.04       ( ![B:$i]:
% 2.82/3.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.82/3.04  thf('17', plain,
% 2.82/3.04      (![X27 : $i, X28 : $i]:
% 2.82/3.04         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 2.82/3.04          | (v1_relat_1 @ X27)
% 2.82/3.04          | ~ (v1_relat_1 @ X28))),
% 2.82/3.04      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.82/3.04  thf('18', plain,
% 2.82/3.04      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.82/3.04      inference('sup-', [status(thm)], ['16', '17'])).
% 2.82/3.04  thf(fc6_relat_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.82/3.04  thf('19', plain,
% 2.82/3.04      (![X34 : $i, X35 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X34 @ X35))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.82/3.04  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 2.82/3.04      inference('demod', [status(thm)], ['18', '19'])).
% 2.82/3.04  thf('21', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 2.82/3.04      inference('demod', [status(thm)], ['15', '20'])).
% 2.82/3.04  thf(t1_xboole_1, axiom,
% 2.82/3.04    (![A:$i,B:$i,C:$i]:
% 2.82/3.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.82/3.04       ( r1_tarski @ A @ C ) ))).
% 2.82/3.04  thf('22', plain,
% 2.82/3.04      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.82/3.04         (~ (r1_tarski @ X3 @ X4)
% 2.82/3.04          | ~ (r1_tarski @ X4 @ X5)
% 2.82/3.04          | (r1_tarski @ X3 @ X5))),
% 2.82/3.04      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.82/3.04  thf('23', plain,
% 2.82/3.04      (![X0 : $i]:
% 2.82/3.04         ((r1_tarski @ (k2_relat_1 @ sk_C) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 2.82/3.04      inference('sup-', [status(thm)], ['21', '22'])).
% 2.82/3.04  thf('24', plain,
% 2.82/3.04      (![X0 : $i]:
% 2.82/3.04         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0))),
% 2.82/3.04      inference('sup-', [status(thm)], ['10', '23'])).
% 2.82/3.04  thf('25', plain,
% 2.82/3.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.04  thf('26', plain,
% 2.82/3.04      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.82/3.04         ((v4_relat_1 @ X36 @ X37)
% 2.82/3.04          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 2.82/3.04      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.82/3.04  thf('27', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 2.82/3.04      inference('sup-', [status(thm)], ['25', '26'])).
% 2.82/3.04  thf(d18_relat_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ B ) =>
% 2.82/3.04       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.82/3.04  thf('28', plain,
% 2.82/3.04      (![X29 : $i, X30 : $i]:
% 2.82/3.04         (~ (v4_relat_1 @ X29 @ X30)
% 2.82/3.04          | (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 2.82/3.04          | ~ (v1_relat_1 @ X29))),
% 2.82/3.04      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.82/3.04  thf('29', plain,
% 2.82/3.04      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 2.82/3.04      inference('sup-', [status(thm)], ['27', '28'])).
% 2.82/3.04  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 2.82/3.04      inference('demod', [status(thm)], ['18', '19'])).
% 2.82/3.04  thf('31', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 2.82/3.04      inference('demod', [status(thm)], ['29', '30'])).
% 2.82/3.04  thf(d10_xboole_0, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.82/3.04  thf('32', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.82/3.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.82/3.04  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.82/3.04      inference('simplify', [status(thm)], ['32'])).
% 2.82/3.04  thf(t8_xboole_1, axiom,
% 2.82/3.04    (![A:$i,B:$i,C:$i]:
% 2.82/3.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.82/3.04       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.82/3.04  thf('34', plain,
% 2.82/3.04      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.82/3.04         (~ (r1_tarski @ X11 @ X12)
% 2.82/3.04          | ~ (r1_tarski @ X13 @ X12)
% 2.82/3.04          | (r1_tarski @ (k2_xboole_0 @ X11 @ X13) @ X12))),
% 2.82/3.04      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.82/3.04  thf('35', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 2.82/3.04      inference('sup-', [status(thm)], ['33', '34'])).
% 2.82/3.04  thf('36', plain,
% 2.82/3.04      ((r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)) @ sk_A)),
% 2.82/3.04      inference('sup-', [status(thm)], ['31', '35'])).
% 2.82/3.04  thf('37', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 2.82/3.04      inference('sup+', [status(thm)], ['6', '9'])).
% 2.82/3.04  thf('38', plain,
% 2.82/3.04      (![X0 : $i, X2 : $i]:
% 2.82/3.04         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.82/3.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.82/3.04  thf('39', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.82/3.04          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 2.82/3.04      inference('sup-', [status(thm)], ['37', '38'])).
% 2.82/3.04  thf('40', plain, (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 2.82/3.04      inference('sup-', [status(thm)], ['36', '39'])).
% 2.82/3.04  thf('41', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.82/3.04      inference('sup-', [status(thm)], ['7', '8'])).
% 2.82/3.04  thf('42', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.82/3.04      inference('sup-', [status(thm)], ['7', '8'])).
% 2.82/3.04  thf('43', plain,
% 2.82/3.04      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.82/3.04         (~ (r1_tarski @ X3 @ X4)
% 2.82/3.04          | ~ (r1_tarski @ X4 @ X5)
% 2.82/3.04          | (r1_tarski @ X3 @ X5))),
% 2.82/3.04      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.82/3.04  thf('44', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.04         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 2.82/3.04      inference('sup-', [status(thm)], ['42', '43'])).
% 2.82/3.04  thf('45', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.04         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.82/3.04      inference('sup-', [status(thm)], ['41', '44'])).
% 2.82/3.04  thf('46', plain,
% 2.82/3.04      (![X0 : $i]:
% 2.82/3.04         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 2.82/3.04      inference('sup+', [status(thm)], ['40', '45'])).
% 2.82/3.04  thf('47', plain,
% 2.82/3.04      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.82/3.04         (~ (r1_tarski @ X11 @ X12)
% 2.82/3.04          | ~ (r1_tarski @ X13 @ X12)
% 2.82/3.04          | (r1_tarski @ (k2_xboole_0 @ X11 @ X13) @ X12))),
% 2.82/3.04      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.82/3.04  thf('48', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 2.82/3.04           (k2_xboole_0 @ X0 @ sk_A))
% 2.82/3.04          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_A)))),
% 2.82/3.04      inference('sup-', [status(thm)], ['46', '47'])).
% 2.82/3.04  thf('49', plain,
% 2.82/3.04      ((r1_tarski @ 
% 2.82/3.04        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 2.82/3.04        (k2_xboole_0 @ sk_B @ sk_A))),
% 2.82/3.04      inference('sup-', [status(thm)], ['24', '48'])).
% 2.82/3.04  thf('50', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.82/3.04      inference('sup+', [status(thm)], ['4', '5'])).
% 2.82/3.04  thf('51', plain,
% 2.82/3.04      ((r1_tarski @ 
% 2.82/3.04        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 2.82/3.04        (k2_xboole_0 @ sk_A @ sk_B))),
% 2.82/3.04      inference('demod', [status(thm)], ['49', '50'])).
% 2.82/3.04  thf('52', plain,
% 2.82/3.04      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 2.82/3.04        | ~ (v1_relat_1 @ sk_C))),
% 2.82/3.04      inference('sup+', [status(thm)], ['1', '51'])).
% 2.82/3.04  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 2.82/3.04      inference('demod', [status(thm)], ['18', '19'])).
% 2.82/3.04  thf('54', plain,
% 2.82/3.04      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 2.82/3.04      inference('demod', [status(thm)], ['52', '53'])).
% 2.82/3.04  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 2.82/3.04  
% 2.82/3.04  % SZS output end Refutation
% 2.82/3.04  
% 2.82/3.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
