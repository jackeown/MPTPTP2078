%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NiRd8swReX

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:37 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 187 expanded)
%              Number of leaves         :   21 (  66 expanded)
%              Depth                    :   22
%              Number of atoms          :  416 (1503 expanded)
%              Number of equality atoms :    9 (  42 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t8_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X18: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('7',plain,(
    r1_tarski @ sk_C_2 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_C_2 )
      | ( r2_hidden @ X19 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X19 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_1 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_1 )
    | ( r1_tarski @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_C_2 @ sk_B_1 ),
    inference(simplify,[status(thm)],['22'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('25',plain,
    ( ( sk_C_2 = sk_B_1 )
    | ( r2_xboole_0 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_xboole_0 @ sk_C_2 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('29',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X18: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('34',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('36',plain,(
    r1_tarski @ sk_B_1 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('38',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('43',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_B_1 )
      | ( r2_hidden @ X19 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X19 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('47',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_2 ) @ sk_C_2 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_xboole_0 @ X10 @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('49',plain,(
    ~ ( r2_xboole_0 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_xboole_0 @ sk_C_2 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NiRd8swReX
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:25:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.71  % Solved by: fo/fo7.sh
% 0.48/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.71  % done 333 iterations in 0.247s
% 0.48/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.71  % SZS output start Refutation
% 0.48/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.48/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.71  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.48/0.71  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.48/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.71  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.48/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.71  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.48/0.71  thf(d3_tarski, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.48/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.48/0.71  thf('0', plain,
% 0.48/0.71      (![X4 : $i, X6 : $i]:
% 0.48/0.71         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.48/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.71  thf(t8_subset_1, conjecture,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.71       ( ![C:$i]:
% 0.48/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.71           ( ( ![D:$i]:
% 0.48/0.71               ( ( m1_subset_1 @ D @ A ) =>
% 0.48/0.71                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.48/0.71             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.48/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.71    (~( ![A:$i,B:$i]:
% 0.48/0.71        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.71          ( ![C:$i]:
% 0.48/0.71            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.71              ( ( ![D:$i]:
% 0.48/0.71                  ( ( m1_subset_1 @ D @ A ) =>
% 0.48/0.71                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.48/0.71                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.48/0.71    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.48/0.71  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(d2_subset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( ( v1_xboole_0 @ A ) =>
% 0.48/0.71         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.48/0.71       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.71         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.71  thf('2', plain,
% 0.48/0.71      (![X15 : $i, X16 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X15 @ X16)
% 0.48/0.71          | (r2_hidden @ X15 @ X16)
% 0.48/0.71          | (v1_xboole_0 @ X16))),
% 0.48/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.48/0.71  thf('3', plain,
% 0.48/0.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.71        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.71  thf(fc1_subset_1, axiom,
% 0.48/0.71    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.48/0.71  thf('4', plain, (![X18 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.48/0.71      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.48/0.71  thf('5', plain, ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.71      inference('clc', [status(thm)], ['3', '4'])).
% 0.48/0.71  thf(l49_zfmisc_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.48/0.71  thf('6', plain,
% 0.48/0.71      (![X12 : $i, X13 : $i]:
% 0.48/0.71         ((r1_tarski @ X12 @ (k3_tarski @ X13)) | ~ (r2_hidden @ X12 @ X13))),
% 0.48/0.71      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.48/0.71  thf('7', plain, ((r1_tarski @ sk_C_2 @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.71  thf(t99_zfmisc_1, axiom,
% 0.48/0.71    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.48/0.71  thf('8', plain, (![X14 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X14)) = (X14))),
% 0.48/0.71      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.48/0.71  thf('9', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 0.48/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.71  thf('10', plain,
% 0.48/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X3 @ X4)
% 0.48/0.71          | (r2_hidden @ X3 @ X5)
% 0.48/0.71          | ~ (r1_tarski @ X4 @ X5))),
% 0.48/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.71  thf('11', plain,
% 0.48/0.71      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.48/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.48/0.71  thf('12', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((r1_tarski @ sk_C_2 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['0', '11'])).
% 0.48/0.71  thf('13', plain,
% 0.48/0.71      (![X15 : $i, X16 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X15 @ X16)
% 0.48/0.71          | (m1_subset_1 @ X15 @ X16)
% 0.48/0.71          | (v1_xboole_0 @ X16))),
% 0.48/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.48/0.71  thf(d1_xboole_0, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.71  thf('14', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.48/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.71  thf('15', plain,
% 0.48/0.71      (![X15 : $i, X16 : $i]:
% 0.48/0.71         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.48/0.71      inference('clc', [status(thm)], ['13', '14'])).
% 0.48/0.71  thf('16', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((r1_tarski @ sk_C_2 @ X0)
% 0.48/0.71          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_2) @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['12', '15'])).
% 0.48/0.71  thf('17', plain,
% 0.48/0.71      (![X19 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X19 @ sk_C_2)
% 0.48/0.71          | (r2_hidden @ X19 @ sk_B_1)
% 0.48/0.71          | ~ (m1_subset_1 @ X19 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('18', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((r1_tarski @ sk_C_2 @ X0)
% 0.48/0.71          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_1)
% 0.48/0.71          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_C_2))),
% 0.48/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.71  thf('19', plain,
% 0.48/0.71      (![X4 : $i, X6 : $i]:
% 0.48/0.71         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.48/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.71  thf('20', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_1)
% 0.48/0.71          | (r1_tarski @ sk_C_2 @ X0))),
% 0.48/0.71      inference('clc', [status(thm)], ['18', '19'])).
% 0.48/0.71  thf('21', plain,
% 0.48/0.71      (![X4 : $i, X6 : $i]:
% 0.48/0.71         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.48/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.71  thf('22', plain,
% 0.48/0.71      (((r1_tarski @ sk_C_2 @ sk_B_1) | (r1_tarski @ sk_C_2 @ sk_B_1))),
% 0.48/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.71  thf('23', plain, ((r1_tarski @ sk_C_2 @ sk_B_1)),
% 0.48/0.71      inference('simplify', [status(thm)], ['22'])).
% 0.48/0.71  thf(d8_xboole_0, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.48/0.71       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.48/0.71  thf('24', plain,
% 0.48/0.71      (![X7 : $i, X9 : $i]:
% 0.48/0.71         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.48/0.71      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.48/0.71  thf('25', plain, ((((sk_C_2) = (sk_B_1)) | (r2_xboole_0 @ sk_C_2 @ sk_B_1))),
% 0.48/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.48/0.71  thf('26', plain, (((sk_B_1) != (sk_C_2))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('27', plain, ((r2_xboole_0 @ sk_C_2 @ sk_B_1)),
% 0.48/0.71      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.48/0.71  thf(t6_xboole_0, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.48/0.71          ( ![C:$i]:
% 0.48/0.71            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.48/0.71  thf('28', plain,
% 0.48/0.71      (![X10 : $i, X11 : $i]:
% 0.48/0.71         (~ (r2_xboole_0 @ X10 @ X11)
% 0.48/0.71          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.48/0.71      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.48/0.71  thf('29', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_B_1)),
% 0.48/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.71  thf('30', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('31', plain,
% 0.48/0.71      (![X15 : $i, X16 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X15 @ X16)
% 0.48/0.71          | (r2_hidden @ X15 @ X16)
% 0.48/0.71          | (v1_xboole_0 @ X16))),
% 0.48/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.48/0.71  thf('32', plain,
% 0.48/0.71      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.71        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['30', '31'])).
% 0.48/0.71  thf('33', plain, (![X18 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.48/0.71      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.48/0.71  thf('34', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.71      inference('clc', [status(thm)], ['32', '33'])).
% 0.48/0.71  thf('35', plain,
% 0.48/0.71      (![X12 : $i, X13 : $i]:
% 0.48/0.71         ((r1_tarski @ X12 @ (k3_tarski @ X13)) | ~ (r2_hidden @ X12 @ X13))),
% 0.48/0.71      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.48/0.71  thf('36', plain, ((r1_tarski @ sk_B_1 @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.48/0.71  thf('37', plain, (![X14 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X14)) = (X14))),
% 0.48/0.71      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.48/0.71  thf('38', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.48/0.71      inference('demod', [status(thm)], ['36', '37'])).
% 0.48/0.71  thf('39', plain,
% 0.48/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X3 @ X4)
% 0.48/0.71          | (r2_hidden @ X3 @ X5)
% 0.48/0.71          | ~ (r1_tarski @ X4 @ X5))),
% 0.48/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.71  thf('40', plain,
% 0.48/0.71      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.48/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.48/0.71  thf('41', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_A)),
% 0.48/0.71      inference('sup-', [status(thm)], ['29', '40'])).
% 0.48/0.71  thf('42', plain,
% 0.48/0.71      (![X15 : $i, X16 : $i]:
% 0.48/0.71         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.48/0.71      inference('clc', [status(thm)], ['13', '14'])).
% 0.48/0.71  thf('43', plain, ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_A)),
% 0.48/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.48/0.71  thf('44', plain,
% 0.48/0.71      (![X19 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X19 @ sk_B_1)
% 0.48/0.71          | (r2_hidden @ X19 @ sk_C_2)
% 0.48/0.71          | ~ (m1_subset_1 @ X19 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('45', plain,
% 0.48/0.71      (((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_C_2)
% 0.48/0.71        | ~ (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_B_1))),
% 0.48/0.71      inference('sup-', [status(thm)], ['43', '44'])).
% 0.48/0.71  thf('46', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_B_1)),
% 0.48/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.71  thf('47', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_2) @ sk_C_2)),
% 0.48/0.71      inference('demod', [status(thm)], ['45', '46'])).
% 0.48/0.71  thf('48', plain,
% 0.48/0.71      (![X10 : $i, X11 : $i]:
% 0.48/0.71         (~ (r2_xboole_0 @ X10 @ X11)
% 0.48/0.71          | ~ (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.48/0.71      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.48/0.71  thf('49', plain, (~ (r2_xboole_0 @ sk_C_2 @ sk_B_1)),
% 0.48/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.48/0.71  thf('50', plain, ((r2_xboole_0 @ sk_C_2 @ sk_B_1)),
% 0.48/0.71      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.48/0.71  thf('51', plain, ($false), inference('demod', [status(thm)], ['49', '50'])).
% 0.48/0.71  
% 0.48/0.71  % SZS output end Refutation
% 0.48/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
