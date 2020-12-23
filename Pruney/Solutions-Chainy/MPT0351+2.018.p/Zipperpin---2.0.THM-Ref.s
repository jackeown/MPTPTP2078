%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hYGmvS9xZR

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:59 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 122 expanded)
%              Number of leaves         :   35 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  535 ( 782 expanded)
%              Number of equality atoms :   49 (  68 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X58: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X58 ) @ ( k1_zfmisc_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X57: $i] :
      ( ( k2_subset_1 @ X57 )
      = X57 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X58: $i] :
      ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X58 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) )
      | ( ( k4_subset_1 @ X62 @ X61 @ X63 )
        = ( k2_xboole_0 @ X61 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ X55 )
      | ( r2_hidden @ X54 @ X55 )
      | ( v1_xboole_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X60: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X50 @ X49 )
      | ( r1_tarski @ X50 @ X48 )
      | ( X49
       != ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X48: $i,X50: $i] :
      ( ( r1_tarski @ X50 @ X48 )
      | ~ ( r2_hidden @ X50 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('27',plain,(
    ! [X59: $i] :
      ( m1_subset_1 @ ( sk_B @ X59 ) @ X59 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('28',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ X55 )
      | ( r2_hidden @ X54 @ X55 )
      | ( v1_xboole_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('31',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['33','42'])).

thf('44',plain,(
    v1_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','43'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ( X14 = X15 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['26','48','49'])).

thf('51',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','50'])).

thf('52',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X57: $i] :
      ( ( k2_subset_1 @ X57 )
      = X57 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,(
    ! [X57: $i] :
      ( ( k2_subset_1 @ X57 )
      = X57 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('55',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hYGmvS9xZR
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 259 iterations in 0.140s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.43/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(dt_k2_subset_1, axiom,
% 0.43/0.61    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (![X58 : $i]: (m1_subset_1 @ (k2_subset_1 @ X58) @ (k1_zfmisc_1 @ X58))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.43/0.61  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.43/0.61  thf('1', plain, (![X57 : $i]: ((k2_subset_1 @ X57) = (X57))),
% 0.43/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.43/0.61  thf('2', plain, (![X58 : $i]: (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X58))),
% 0.43/0.61      inference('demod', [status(thm)], ['0', '1'])).
% 0.43/0.61  thf(t28_subset_1, conjecture,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.61       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i]:
% 0.43/0.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.61          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.43/0.61  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(redefinition_k4_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.43/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.43/0.61       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62))
% 0.43/0.61          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62))
% 0.43/0.61          | ((k4_subset_1 @ X62 @ X61 @ X63) = (k2_xboole_0 @ X61 @ X63)))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0) = (k2_xboole_0 @ sk_B_1 @ X0))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['2', '5'])).
% 0.43/0.61  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(d2_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( v1_xboole_0 @ A ) =>
% 0.43/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.43/0.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.43/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X54 : $i, X55 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X54 @ X55)
% 0.43/0.61          | (r2_hidden @ X54 @ X55)
% 0.43/0.61          | (v1_xboole_0 @ X55))),
% 0.43/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.61        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.61  thf(fc1_subset_1, axiom,
% 0.43/0.61    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.43/0.61  thf('10', plain, (![X60 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X60))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.43/0.61  thf('11', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['9', '10'])).
% 0.43/0.61  thf(d1_zfmisc_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.43/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X50 @ X49)
% 0.43/0.61          | (r1_tarski @ X50 @ X48)
% 0.43/0.61          | ((X49) != (k1_zfmisc_1 @ X48)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X48 : $i, X50 : $i]:
% 0.43/0.61         ((r1_tarski @ X50 @ X48) | ~ (r2_hidden @ X50 @ (k1_zfmisc_1 @ X48)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['12'])).
% 0.43/0.61  thf('14', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['11', '13'])).
% 0.43/0.61  thf(t28_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i]:
% 0.43/0.61         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.61  thf('16', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.61  thf(t100_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X9 @ X10)
% 0.43/0.61           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['16', '17'])).
% 0.43/0.61  thf(t98_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         ((k2_xboole_0 @ X16 @ X17)
% 0.43/0.61           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (((k2_xboole_0 @ sk_A @ sk_B_1)
% 0.43/0.61         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B_1 @ sk_B_1)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['18', '19'])).
% 0.43/0.61  thf(commutativity_k2_tarski, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.43/0.61  thf(l51_zfmisc_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X52 : $i, X53 : $i]:
% 0.43/0.61         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.43/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (![X52 : $i, X53 : $i]:
% 0.43/0.61         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.43/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['23', '24'])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (((k2_xboole_0 @ sk_B_1 @ sk_A)
% 0.43/0.61         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B_1 @ sk_B_1)))),
% 0.43/0.61      inference('demod', [status(thm)], ['20', '25'])).
% 0.43/0.61  thf(existence_m1_subset_1, axiom,
% 0.43/0.61    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.43/0.61  thf('27', plain, (![X59 : $i]: (m1_subset_1 @ (sk_B @ X59) @ X59)),
% 0.43/0.61      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (![X54 : $i, X55 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X54 @ X55)
% 0.43/0.61          | (r2_hidden @ X54 @ X55)
% 0.43/0.61          | (v1_xboole_0 @ X55))),
% 0.43/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['16', '17'])).
% 0.43/0.61  thf(d5_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.43/0.61       ( ![D:$i]:
% 0.43/0.61         ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.61           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X4 @ X3)
% 0.43/0.61          | (r2_hidden @ X4 @ X1)
% 0.43/0.61          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.43/0.61         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_B_1 @ sk_B_1))
% 0.43/0.61          | (r2_hidden @ X0 @ sk_B_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['30', '32'])).
% 0.43/0.61  thf(d10_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('35', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.43/0.61      inference('simplify', [status(thm)], ['34'])).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i]:
% 0.43/0.61         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.61  thf('37', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.43/0.61  thf('38', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X9 @ X10)
% 0.43/0.61           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['37', '38'])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X4 @ X3)
% 0.43/0.61          | ~ (r2_hidden @ X4 @ X2)
% 0.43/0.61          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X4 @ X2)
% 0.43/0.61          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['40'])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.43/0.61          | ~ (r2_hidden @ X1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['39', '41'])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.43/0.61      inference('clc', [status(thm)], ['33', '42'])).
% 0.43/0.61  thf('44', plain, ((v1_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['29', '43'])).
% 0.43/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.43/0.61  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.61  thf(t8_boole, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i]:
% 0.43/0.61         (~ (v1_xboole_0 @ X14) | ~ (v1_xboole_0 @ X15) | ((X14) = (X15)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t8_boole])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.43/0.61  thf('48', plain, (((k1_xboole_0) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['44', '47'])).
% 0.43/0.61  thf(t5_boole, axiom,
% 0.43/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.61  thf('49', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.43/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.43/0.61  thf('50', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['26', '48', '49'])).
% 0.43/0.61  thf('51', plain, (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) = (sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '50'])).
% 0.43/0.61  thf('52', plain,
% 0.43/0.61      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k2_subset_1 @ sk_A))
% 0.43/0.61         != (k2_subset_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('53', plain, (![X57 : $i]: ((k2_subset_1 @ X57) = (X57))),
% 0.43/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.43/0.61  thf('54', plain, (![X57 : $i]: ((k2_subset_1 @ X57) = (X57))),
% 0.43/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.43/0.61  thf('55', plain, (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) != (sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.43/0.61  thf('56', plain, ($false),
% 0.43/0.61      inference('simplify_reflect-', [status(thm)], ['51', '55'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
