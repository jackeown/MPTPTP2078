%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cE1NVdGJjx

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:12 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 110 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  500 ( 872 expanded)
%              Number of equality atoms :   33 (  83 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t8_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( X13 = X11 )
      | ( r2_hidden @ ( sk_D @ X11 @ X13 @ X12 ) @ X13 )
      | ( r2_hidden @ ( sk_D @ X11 @ X13 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_setfam_1 @ X19 @ ( k7_setfam_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('9',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( X14
       != ( k7_setfam_1 @ X15 @ X16 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X15 @ X17 ) @ X16 )
      | ~ ( r2_hidden @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r2_hidden @ X17 @ ( k7_setfam_1 @ X15 @ X16 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X15 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('17',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('20',plain,(
    ! [X20: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X8 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ ( k1_tarski @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X7 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( m1_subset_1 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(clc,[status(thm)],['33','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['6','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('40',plain,(
    $false ),
    inference('sup-',[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cE1NVdGJjx
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 221 iterations in 0.125s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.60  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.40/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(t46_setfam_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.60       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i]:
% 0.40/0.60        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.60          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t4_subset_1, axiom,
% 0.40/0.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.60  thf(t8_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.60       ( ![C:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.60           ( ( ![D:$i]:
% 0.40/0.60               ( ( m1_subset_1 @ D @ A ) =>
% 0.40/0.60                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.40/0.60             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.40/0.60          | ((X13) = (X11))
% 0.40/0.60          | (r2_hidden @ (sk_D @ X11 @ X13 @ X12) @ X13)
% 0.40/0.60          | (r2_hidden @ (sk_D @ X11 @ X13 @ X12) @ X11)
% 0.40/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.40/0.60          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.40/0.60          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.40/0.60          | ((X1) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      ((((sk_B) = (k1_xboole_0))
% 0.40/0.60        | (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.40/0.60           sk_B)
% 0.40/0.60        | (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.40/0.60           k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '3'])).
% 0.40/0.60  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.40/0.60        | (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.40/0.60           k1_xboole_0))),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(involutiveness_k7_setfam_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.60       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i]:
% 0.40/0.60         (((k7_setfam_1 @ X19 @ (k7_setfam_1 @ X19 @ X18)) = (X18))
% 0.40/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.40/0.60      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.60  thf('10', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('11', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.60  thf(d8_setfam_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.60       ( ![C:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.60           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.40/0.60             ( ![D:$i]:
% 0.40/0.60               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.60                 ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.60                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.40/0.60          | ((X14) != (k7_setfam_1 @ X15 @ X16))
% 0.40/0.60          | (r2_hidden @ (k3_subset_1 @ X15 @ X17) @ X16)
% 0.40/0.60          | ~ (r2_hidden @ X17 @ X14)
% 0.40/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X15))
% 0.40/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.40/0.60      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.40/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X15))
% 0.40/0.60          | ~ (r2_hidden @ X17 @ (k7_setfam_1 @ X15 @ X16))
% 0.40/0.60          | (r2_hidden @ (k3_subset_1 @ X15 @ X17) @ X16)
% 0.40/0.60          | ~ (m1_subset_1 @ (k7_setfam_1 @ X15 @ X16) @ 
% 0.40/0.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.40/0.60          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.40/0.60          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.60          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('16', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.40/0.60          | ~ (r2_hidden @ X0 @ sk_B)
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.60      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.40/0.60  thf(t69_enumset1, axiom,
% 0.40/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.60  thf('19', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.60  thf(t11_setfam_1, axiom,
% 0.40/0.60    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.40/0.60  thf('20', plain, (![X20 : $i]: ((k1_setfam_1 @ (k1_tarski @ X20)) = (X20))),
% 0.40/0.60      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['19', '20'])).
% 0.40/0.60  thf(t12_setfam_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      (![X21 : $i, X22 : $i]:
% 0.40/0.60         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 0.40/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.60  thf('23', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.60  thf(t100_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['23', '24'])).
% 0.40/0.60  thf('26', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.60  thf(t64_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.40/0.60       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.60         (((X6) != (X8))
% 0.40/0.60          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ (k1_tarski @ X8))))),
% 0.40/0.60      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      (![X7 : $i, X8 : $i]:
% 0.40/0.60         ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X7 @ (k1_tarski @ X8)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['26', '28'])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ~ (r2_hidden @ X0 @ 
% 0.40/0.60            (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['25', '29'])).
% 0.40/0.60  thf(t92_xboole_1, axiom,
% 0.40/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.60  thf('31', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.60  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.60          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.40/0.60      inference('clc', [status(thm)], ['18', '32'])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t4_subset, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.40/0.60       ( m1_subset_1 @ A @ C ) ))).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X23 @ X24)
% 0.40/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.40/0.60          | (m1_subset_1 @ X23 @ X25))),
% 0.40/0.60      inference('cnf', [status(esa)], [t4_subset])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.60  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.40/0.60      inference('clc', [status(thm)], ['33', '36'])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      ((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.40/0.60        k1_xboole_0)),
% 0.40/0.60      inference('clc', [status(thm)], ['6', '37'])).
% 0.40/0.60  thf('39', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.60  thf('40', plain, ($false), inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
