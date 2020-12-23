%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VpQx3qP6CZ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:43 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 190 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  483 (1448 expanded)
%              Number of equality atoms :   39 ( 124 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    | ( sk_B_1
      = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('21',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','34','35'])).

thf('37',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_B_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('40',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','43'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_C ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ sk_B_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['47','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['38','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VpQx3qP6CZ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 136 iterations in 0.092s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(t40_subset_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.36/0.55         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.55        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55          ( ( ( r1_tarski @ B @ C ) & 
% 0.36/0.55              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.36/0.55            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.36/0.55  thf('0', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d5_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i]:
% 0.36/0.55         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.36/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.55  thf(t106_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.36/0.55       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.55         ((r1_tarski @ X12 @ X13)
% 0.36/0.55          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.36/0.55          | (r1_tarski @ X0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf('6', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '5'])).
% 0.36/0.55  thf(t28_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i]:
% 0.36/0.55         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.55  thf('8', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.55  thf(t100_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X10 @ X11)
% 0.36/0.55           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf(d10_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('12', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.36/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.55         ((r1_tarski @ X12 @ X13)
% 0.36/0.55          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.36/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X7 : $i, X9 : $i]:
% 0.36/0.55         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.55          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      ((~ (r1_tarski @ sk_B_1 @ (k5_xboole_0 @ sk_B_1 @ sk_B_1))
% 0.36/0.55        | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '16'])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      ((~ (r1_tarski @ sk_B_1 @ (k5_xboole_0 @ sk_B_1 @ sk_B_1))
% 0.36/0.55        | ((sk_B_1) = (k5_xboole_0 @ sk_B_1 @ sk_B_1)))),
% 0.36/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.55  thf(t7_xboole_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.55  thf('21', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.36/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i]:
% 0.36/0.55         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.55  thf('23', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X10 @ X11)
% 0.36/0.55           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf(d5_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.36/0.55          | (r2_hidden @ X4 @ X1)
% 0.36/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.55         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['25', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.36/0.55          | ~ (r2_hidden @ X4 @ X2)
% 0.36/0.55          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.36/0.55          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['30'])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.36/0.55          | ~ (r2_hidden @ X1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '31'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('clc', [status(thm)], ['28', '32'])).
% 0.36/0.55  thf('34', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '33'])).
% 0.36/0.55  thf('35', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '33'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      ((~ (r1_tarski @ sk_B_1 @ k1_xboole_0) | ((sk_B_1) = (k1_xboole_0)))),
% 0.36/0.55      inference('demod', [status(thm)], ['19', '34', '35'])).
% 0.36/0.55  thf('37', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('38', plain, (~ (r1_tarski @ sk_B_1 @ k1_xboole_0)),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.36/0.55  thf('39', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.36/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.55  thf('40', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ X12 @ X14)
% 0.36/0.55          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.36/0.55          | (r1_xboole_0 @ X0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf('44', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C)),
% 0.36/0.55      inference('sup-', [status(thm)], ['40', '43'])).
% 0.36/0.55  thf(t86_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.36/0.55       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X17 @ X18)
% 0.36/0.55          | ~ (r1_xboole_0 @ X17 @ X19)
% 0.36/0.55          | (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X19)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r1_tarski @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_C))
% 0.36/0.55          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.55  thf('47', plain, ((r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['39', '46'])).
% 0.36/0.55  thf('48', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i]:
% 0.36/0.55         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.55  thf('50', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C) = (sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.55  thf('51', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X10 @ X11)
% 0.36/0.55           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.55  thf('52', plain,
% 0.36/0.55      (((k4_xboole_0 @ sk_B_1 @ sk_C) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['50', '51'])).
% 0.36/0.55  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '33'])).
% 0.36/0.55  thf('54', plain, (((k4_xboole_0 @ sk_B_1 @ sk_C) = (k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.55  thf('55', plain, ((r1_tarski @ sk_B_1 @ k1_xboole_0)),
% 0.36/0.55      inference('demod', [status(thm)], ['47', '54'])).
% 0.36/0.55  thf('56', plain, ($false), inference('demod', [status(thm)], ['38', '55'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
