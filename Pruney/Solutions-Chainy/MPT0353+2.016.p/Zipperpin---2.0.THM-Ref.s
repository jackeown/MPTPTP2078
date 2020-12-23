%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e3UExA9J8L

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:15 EST 2020

% Result     : Theorem 9.92s
% Output     : Refutation 9.92s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 186 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  582 (1821 expanded)
%              Number of equality atoms :   53 ( 142 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('0',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('31',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k9_subset_1 @ X23 @ X21 @ X22 )
        = ( k3_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('46',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['34','53'])).

thf('55',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['28','33','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e3UExA9J8L
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 9.92/10.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.92/10.10  % Solved by: fo/fo7.sh
% 9.92/10.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.92/10.10  % done 2422 iterations in 9.644s
% 9.92/10.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.92/10.10  % SZS output start Refutation
% 9.92/10.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.92/10.10  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 9.92/10.10  thf(sk_A_type, type, sk_A: $i).
% 9.92/10.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.92/10.10  thf(sk_C_type, type, sk_C: $i).
% 9.92/10.10  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 9.92/10.10  thf(sk_B_type, type, sk_B: $i).
% 9.92/10.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.92/10.10  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 9.92/10.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.92/10.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 9.92/10.10  thf(t32_subset_1, conjecture,
% 9.92/10.10    (![A:$i,B:$i]:
% 9.92/10.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.92/10.10       ( ![C:$i]:
% 9.92/10.10         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.92/10.10           ( ( k7_subset_1 @ A @ B @ C ) =
% 9.92/10.10             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 9.92/10.10  thf(zf_stmt_0, negated_conjecture,
% 9.92/10.10    (~( ![A:$i,B:$i]:
% 9.92/10.10        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.92/10.10          ( ![C:$i]:
% 9.92/10.10            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.92/10.10              ( ( k7_subset_1 @ A @ B @ C ) =
% 9.92/10.10                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 9.92/10.10    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 9.92/10.10  thf('0', plain,
% 9.92/10.10      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 9.92/10.10         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 9.92/10.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.10  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.10  thf(redefinition_k7_subset_1, axiom,
% 9.92/10.10    (![A:$i,B:$i,C:$i]:
% 9.92/10.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.92/10.10       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 9.92/10.10  thf('2', plain,
% 9.92/10.10      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.92/10.10         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 9.92/10.10          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 9.92/10.10      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 9.92/10.10  thf('3', plain,
% 9.92/10.10      (![X0 : $i]:
% 9.92/10.10         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 9.92/10.10      inference('sup-', [status(thm)], ['1', '2'])).
% 9.92/10.10  thf('4', plain,
% 9.92/10.10      (((k4_xboole_0 @ sk_B @ sk_C)
% 9.92/10.10         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 9.92/10.10      inference('demod', [status(thm)], ['0', '3'])).
% 9.92/10.10  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.10  thf(dt_k3_subset_1, axiom,
% 9.92/10.10    (![A:$i,B:$i]:
% 9.92/10.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.92/10.10       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.92/10.10  thf('6', plain,
% 9.92/10.10      (![X14 : $i, X15 : $i]:
% 9.92/10.10         ((m1_subset_1 @ (k3_subset_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 9.92/10.10          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 9.92/10.10      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.92/10.10  thf('7', plain,
% 9.92/10.10      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('sup-', [status(thm)], ['5', '6'])).
% 9.92/10.10  thf(d5_subset_1, axiom,
% 9.92/10.10    (![A:$i,B:$i]:
% 9.92/10.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.92/10.10       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 9.92/10.10  thf('8', plain,
% 9.92/10.10      (![X12 : $i, X13 : $i]:
% 9.92/10.10         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 9.92/10.10          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 9.92/10.10      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.92/10.10  thf('9', plain,
% 9.92/10.10      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 9.92/10.10         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 9.92/10.10      inference('sup-', [status(thm)], ['7', '8'])).
% 9.92/10.10  thf('10', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.10  thf(involutiveness_k3_subset_1, axiom,
% 9.92/10.10    (![A:$i,B:$i]:
% 9.92/10.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.92/10.10       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 9.92/10.10  thf('11', plain,
% 9.92/10.10      (![X16 : $i, X17 : $i]:
% 9.92/10.10         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 9.92/10.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 9.92/10.10      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.92/10.10  thf('12', plain,
% 9.92/10.10      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 9.92/10.10      inference('sup-', [status(thm)], ['10', '11'])).
% 9.92/10.10  thf('13', plain,
% 9.92/10.10      (((sk_C) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 9.92/10.10      inference('demod', [status(thm)], ['9', '12'])).
% 9.92/10.10  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.10  thf('15', plain,
% 9.92/10.10      (![X12 : $i, X13 : $i]:
% 9.92/10.10         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 9.92/10.10          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 9.92/10.10      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.92/10.10  thf('16', plain,
% 9.92/10.10      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 9.92/10.10      inference('sup-', [status(thm)], ['14', '15'])).
% 9.92/10.10  thf(t48_xboole_1, axiom,
% 9.92/10.10    (![A:$i,B:$i]:
% 9.92/10.10     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.92/10.10  thf('17', plain,
% 9.92/10.10      (![X7 : $i, X8 : $i]:
% 9.92/10.10         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 9.92/10.10           = (k3_xboole_0 @ X7 @ X8))),
% 9.92/10.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.92/10.10  thf('18', plain,
% 9.92/10.10      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 9.92/10.10         = (k3_xboole_0 @ sk_A @ sk_C))),
% 9.92/10.10      inference('sup+', [status(thm)], ['16', '17'])).
% 9.92/10.10  thf(commutativity_k3_xboole_0, axiom,
% 9.92/10.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 9.92/10.10  thf('19', plain,
% 9.92/10.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.92/10.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.92/10.10  thf('20', plain,
% 9.92/10.10      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 9.92/10.10         = (k3_xboole_0 @ sk_C @ sk_A))),
% 9.92/10.10      inference('demod', [status(thm)], ['18', '19'])).
% 9.92/10.10  thf('21', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_A))),
% 9.92/10.10      inference('sup+', [status(thm)], ['13', '20'])).
% 9.92/10.10  thf('22', plain,
% 9.92/10.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.92/10.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.92/10.10  thf(t100_xboole_1, axiom,
% 9.92/10.10    (![A:$i,B:$i]:
% 9.92/10.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 9.92/10.10  thf('23', plain,
% 9.92/10.10      (![X2 : $i, X3 : $i]:
% 9.92/10.10         ((k4_xboole_0 @ X2 @ X3)
% 9.92/10.10           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 9.92/10.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.92/10.10  thf('24', plain,
% 9.92/10.10      (![X0 : $i, X1 : $i]:
% 9.92/10.10         ((k4_xboole_0 @ X0 @ X1)
% 9.92/10.10           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.92/10.10      inference('sup+', [status(thm)], ['22', '23'])).
% 9.92/10.10  thf('25', plain,
% 9.92/10.10      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 9.92/10.10      inference('sup+', [status(thm)], ['21', '24'])).
% 9.92/10.10  thf('26', plain,
% 9.92/10.10      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 9.92/10.10      inference('sup-', [status(thm)], ['14', '15'])).
% 9.92/10.10  thf('27', plain,
% 9.92/10.10      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 9.92/10.10      inference('sup+', [status(thm)], ['25', '26'])).
% 9.92/10.10  thf('28', plain,
% 9.92/10.10      (((k4_xboole_0 @ sk_B @ sk_C)
% 9.92/10.10         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)))),
% 9.92/10.10      inference('demod', [status(thm)], ['4', '27'])).
% 9.92/10.10  thf('29', plain,
% 9.92/10.10      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('sup-', [status(thm)], ['5', '6'])).
% 9.92/10.10  thf('30', plain,
% 9.92/10.10      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 9.92/10.10      inference('sup+', [status(thm)], ['25', '26'])).
% 9.92/10.10  thf('31', plain,
% 9.92/10.10      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('demod', [status(thm)], ['29', '30'])).
% 9.92/10.10  thf(redefinition_k9_subset_1, axiom,
% 9.92/10.10    (![A:$i,B:$i,C:$i]:
% 9.92/10.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.92/10.10       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 9.92/10.10  thf('32', plain,
% 9.92/10.10      (![X21 : $i, X22 : $i, X23 : $i]:
% 9.92/10.10         (((k9_subset_1 @ X23 @ X21 @ X22) = (k3_xboole_0 @ X21 @ X22))
% 9.92/10.10          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 9.92/10.10      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 9.92/10.10  thf('33', plain,
% 9.92/10.10      (![X0 : $i]:
% 9.92/10.10         ((k9_subset_1 @ sk_A @ X0 @ (k5_xboole_0 @ sk_A @ sk_C))
% 9.92/10.10           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C)))),
% 9.92/10.10      inference('sup-', [status(thm)], ['31', '32'])).
% 9.92/10.10  thf('34', plain,
% 9.92/10.10      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 9.92/10.10      inference('sup+', [status(thm)], ['21', '24'])).
% 9.92/10.10  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.10  thf('36', plain,
% 9.92/10.10      (![X14 : $i, X15 : $i]:
% 9.92/10.10         ((m1_subset_1 @ (k3_subset_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 9.92/10.10          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 9.92/10.10      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.92/10.10  thf('37', plain,
% 9.92/10.10      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('sup-', [status(thm)], ['35', '36'])).
% 9.92/10.10  thf('38', plain,
% 9.92/10.10      (![X12 : $i, X13 : $i]:
% 9.92/10.10         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 9.92/10.10          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 9.92/10.10      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.92/10.10  thf('39', plain,
% 9.92/10.10      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 9.92/10.10         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 9.92/10.10      inference('sup-', [status(thm)], ['37', '38'])).
% 9.92/10.10  thf('40', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.10  thf('41', plain,
% 9.92/10.10      (![X16 : $i, X17 : $i]:
% 9.92/10.10         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 9.92/10.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 9.92/10.10      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.92/10.10  thf('42', plain,
% 9.92/10.10      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 9.92/10.10      inference('sup-', [status(thm)], ['40', '41'])).
% 9.92/10.10  thf('43', plain,
% 9.92/10.10      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 9.92/10.10      inference('demod', [status(thm)], ['39', '42'])).
% 9.92/10.10  thf('44', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.92/10.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.10  thf('45', plain,
% 9.92/10.10      (![X12 : $i, X13 : $i]:
% 9.92/10.10         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 9.92/10.10          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 9.92/10.10      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.92/10.10  thf('46', plain,
% 9.92/10.10      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 9.92/10.10      inference('sup-', [status(thm)], ['44', '45'])).
% 9.92/10.10  thf('47', plain,
% 9.92/10.10      (![X7 : $i, X8 : $i]:
% 9.92/10.10         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 9.92/10.10           = (k3_xboole_0 @ X7 @ X8))),
% 9.92/10.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.92/10.10  thf('48', plain,
% 9.92/10.10      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 9.92/10.10         = (k3_xboole_0 @ sk_A @ sk_B))),
% 9.92/10.10      inference('sup+', [status(thm)], ['46', '47'])).
% 9.92/10.10  thf('49', plain,
% 9.92/10.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.92/10.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.92/10.10  thf('50', plain,
% 9.92/10.10      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 9.92/10.10         = (k3_xboole_0 @ sk_B @ sk_A))),
% 9.92/10.10      inference('demod', [status(thm)], ['48', '49'])).
% 9.92/10.10  thf('51', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 9.92/10.10      inference('sup+', [status(thm)], ['43', '50'])).
% 9.92/10.10  thf(t49_xboole_1, axiom,
% 9.92/10.10    (![A:$i,B:$i,C:$i]:
% 9.92/10.10     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 9.92/10.10       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 9.92/10.10  thf('52', plain,
% 9.92/10.10      (![X9 : $i, X10 : $i, X11 : $i]:
% 9.92/10.10         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 9.92/10.10           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 9.92/10.10      inference('cnf', [status(esa)], [t49_xboole_1])).
% 9.92/10.10  thf('53', plain,
% 9.92/10.10      (![X0 : $i]:
% 9.92/10.10         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 9.92/10.10           = (k4_xboole_0 @ sk_B @ X0))),
% 9.92/10.10      inference('sup+', [status(thm)], ['51', '52'])).
% 9.92/10.10  thf('54', plain,
% 9.92/10.10      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C))
% 9.92/10.10         = (k4_xboole_0 @ sk_B @ sk_C))),
% 9.92/10.10      inference('sup+', [status(thm)], ['34', '53'])).
% 9.92/10.10  thf('55', plain,
% 9.92/10.10      (((k4_xboole_0 @ sk_B @ sk_C) != (k4_xboole_0 @ sk_B @ sk_C))),
% 9.92/10.10      inference('demod', [status(thm)], ['28', '33', '54'])).
% 9.92/10.10  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 9.92/10.10  
% 9.92/10.10  % SZS output end Refutation
% 9.92/10.10  
% 9.92/10.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
