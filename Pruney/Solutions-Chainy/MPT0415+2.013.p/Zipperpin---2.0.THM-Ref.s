%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F6fjsWW0RW

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:11 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 104 expanded)
%              Number of leaves         :   27 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  510 ( 803 expanded)
%              Number of equality atoms :   40 (  78 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( sk_B @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t50_subset_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ( r2_hidden @ X18 @ ( k3_subset_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X10 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X9 @ ( k1_tarski @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X9 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['14','22'])).

thf(t46_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_setfam_1])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k7_setfam_1 @ X24 @ ( k7_setfam_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('26',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) )
      | ( X19
       != ( k7_setfam_1 @ X20 @ X21 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X20 @ X22 ) @ X21 )
      | ~ ( r2_hidden @ X22 @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r2_hidden @ X22 @ ( k7_setfam_1 @ X20 @ X21 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X20 @ X22 ) @ X21 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('34',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['37','40'])).

thf('42',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','41'])).

thf('43',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F6fjsWW0RW
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 216 iterations in 0.108s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(existence_m1_subset_1, axiom,
% 0.36/0.55    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.36/0.55  thf('0', plain, (![X14 : $i]: (m1_subset_1 @ (sk_B @ X14) @ X14)),
% 0.36/0.55      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.36/0.55  thf(t4_subset_1, axiom,
% 0.36/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.55  thf(t50_subset_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( m1_subset_1 @ C @ A ) =>
% 0.36/0.55               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.36/0.55                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.36/0.55          | (r2_hidden @ X18 @ X16)
% 0.36/0.55          | (r2_hidden @ X18 @ (k3_subset_1 @ X17 @ X16))
% 0.36/0.55          | ~ (m1_subset_1 @ X18 @ X17)
% 0.36/0.55          | ((X17) = (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((X0) = (k1_xboole_0))
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ X0)
% 0.36/0.55          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.36/0.55          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.55  thf(d5_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i]:
% 0.36/0.55         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.36/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf(t2_boole, axiom,
% 0.36/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.36/0.55  thf(t100_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X1 @ X2)
% 0.36/0.55           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf(t5_boole, axiom,
% 0.36/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.55  thf('10', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.36/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.55  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf('12', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['6', '11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (((X0) = (k1_xboole_0))
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ X0)
% 0.36/0.55          | (r2_hidden @ X1 @ X0)
% 0.36/0.55          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['3', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r2_hidden @ (sk_B @ X0) @ k1_xboole_0)
% 0.36/0.55          | (r2_hidden @ (sk_B @ X0) @ X0)
% 0.36/0.55          | ((X0) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '13'])).
% 0.36/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.36/0.55  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X1 @ X2)
% 0.36/0.55           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.55  thf(t64_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.36/0.55       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.55         (((X8) != (X10))
% 0.36/0.55          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X9 @ (k1_tarski @ X10))))),
% 0.36/0.55      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i]:
% 0.36/0.55         ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X9 @ (k1_tarski @ X10)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ~ (r2_hidden @ X0 @ 
% 0.36/0.55            (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['17', '19'])).
% 0.36/0.55  thf(t92_xboole_1, axiom,
% 0.36/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.55  thf('21', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.55  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.36/0.55      inference('clc', [status(thm)], ['14', '22'])).
% 0.36/0.55  thf(t46_setfam_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.55       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.55            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i]:
% 0.36/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.55          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.55               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(involutiveness_k7_setfam_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.55       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         (((k7_setfam_1 @ X24 @ (k7_setfam_1 @ X24 @ X23)) = (X23))
% 0.36/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 0.36/0.55      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.55  thf('27', plain, (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('28', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf(d8_setfam_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.55       ( ![C:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.55           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.36/0.55             ( ![D:$i]:
% 0.36/0.55               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55                 ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.55                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20)))
% 0.36/0.55          | ((X19) != (k7_setfam_1 @ X20 @ X21))
% 0.36/0.55          | (r2_hidden @ (k3_subset_1 @ X20 @ X22) @ X21)
% 0.36/0.55          | ~ (r2_hidden @ X22 @ X19)
% 0.36/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X20))
% 0.36/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.36/0.55      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20)))
% 0.36/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X20))
% 0.36/0.55          | ~ (r2_hidden @ X22 @ (k7_setfam_1 @ X20 @ X21))
% 0.36/0.55          | (r2_hidden @ (k3_subset_1 @ X20 @ X22) @ X21)
% 0.36/0.55          | ~ (m1_subset_1 @ (k7_setfam_1 @ X20 @ X21) @ 
% 0.36/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.36/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.36/0.55          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.36/0.55          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.36/0.55          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['28', '30'])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('33', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.36/0.55          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.36/0.55  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.36/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t4_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.36/0.55       ( m1_subset_1 @ A @ C ) ))).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X27 @ X28)
% 0.36/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.36/0.55          | (m1_subset_1 @ X27 @ X29))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.55  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.36/0.55      inference('clc', [status(thm)], ['37', '40'])).
% 0.36/0.55  thf('42', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['23', '41'])).
% 0.36/0.55  thf('43', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('44', plain, ($false),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
