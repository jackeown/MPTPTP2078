%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NUNXN1Z6HV

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:19 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 429 expanded)
%              Number of leaves         :   19 ( 125 expanded)
%              Depth                    :   22
%              Number of atoms          :  543 (3796 expanded)
%              Number of equality atoms :   55 ( 332 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X18: $i] :
      ( ( X18
        = ( k1_tarski @ X14 ) )
      | ( ( sk_C_1 @ X18 @ X14 )
        = X14 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X14 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(t1_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_zfmisc_1 @ B ) )
           => ( ( r1_tarski @ A @ B )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_tex_2])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['7','8'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X42: $i] :
      ( ~ ( v1_zfmisc_1 @ X42 )
      | ( X42
        = ( k6_domain_1 @ X42 @ ( sk_B_1 @ X42 ) ) )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('11',plain,(
    ! [X42: $i] :
      ( ~ ( v1_zfmisc_1 @ X42 )
      | ( m1_subset_1 @ ( sk_B_1 @ X42 ) @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ X40 )
      | ( ( k6_domain_1 @ X40 @ X41 )
        = ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1
        = ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_B_1 @ sk_B_2 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_B_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B @ sk_A )
    = ( sk_B_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('26',plain,
    ( ( sk_B_2
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B_2
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_B_2
    = ( k1_tarski @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( X0
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = X0 )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ sk_A )
       != X0 )
      | ( ( sk_C_1 @ sk_A @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( sk_B_2
    = ( k1_tarski @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('37',plain,
    ( ( sk_A = sk_B_2 )
    | ( ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i,X18: $i] :
      ( ( X18
        = ( k1_tarski @ X14 ) )
      | ( ( sk_C_1 @ X18 @ X14 )
       != X14 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X18 @ X14 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A )
    | ( ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) )
     != ( sk_B @ sk_A ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['7','8'])).

thf('43',plain,
    ( sk_B_2
    = ( k1_tarski @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('44',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,
    ( ( r1_tarski @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ sk_B_2 @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['42','56'])).

thf('58',plain,
    ( ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) )
    = ( sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('59',plain,
    ( sk_B_2
    = ( k1_tarski @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('60',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( sk_A = sk_B_2 ) ),
    inference(demod,[status(thm)],['41','57','58','59'])).

thf('61',plain,(
    sk_A = sk_B_2 ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NUNXN1Z6HV
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.18/1.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.38  % Solved by: fo/fo7.sh
% 1.18/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.38  % done 2463 iterations in 0.882s
% 1.18/1.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.38  % SZS output start Refutation
% 1.18/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.38  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.18/1.38  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.18/1.38  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.18/1.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.38  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.18/1.38  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.18/1.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.18/1.38  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.18/1.38  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.18/1.38  thf(sk_B_type, type, sk_B: $i > $i).
% 1.18/1.38  thf(d1_tarski, axiom,
% 1.18/1.38    (![A:$i,B:$i]:
% 1.18/1.38     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.18/1.38       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.18/1.38  thf('0', plain,
% 1.18/1.38      (![X14 : $i, X18 : $i]:
% 1.18/1.38         (((X18) = (k1_tarski @ X14))
% 1.18/1.38          | ((sk_C_1 @ X18 @ X14) = (X14))
% 1.18/1.38          | (r2_hidden @ (sk_C_1 @ X18 @ X14) @ X18))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_tarski])).
% 1.18/1.38  thf(t1_tex_2, conjecture,
% 1.18/1.38    (![A:$i]:
% 1.18/1.38     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.18/1.38       ( ![B:$i]:
% 1.18/1.38         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.18/1.38           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 1.18/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.38    (~( ![A:$i]:
% 1.18/1.38        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.18/1.38          ( ![B:$i]:
% 1.18/1.38            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.18/1.38              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 1.18/1.38    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 1.18/1.38  thf('1', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf(d3_tarski, axiom,
% 1.18/1.38    (![A:$i,B:$i]:
% 1.18/1.38     ( ( r1_tarski @ A @ B ) <=>
% 1.18/1.38       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.18/1.38  thf('2', plain,
% 1.18/1.38      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X3 @ X4)
% 1.18/1.38          | (r2_hidden @ X3 @ X5)
% 1.18/1.38          | ~ (r1_tarski @ X4 @ X5))),
% 1.18/1.38      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.38  thf('3', plain,
% 1.18/1.38      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.18/1.38      inference('sup-', [status(thm)], ['1', '2'])).
% 1.18/1.38  thf('4', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (((sk_C_1 @ sk_A @ X0) = (X0))
% 1.18/1.38          | ((sk_A) = (k1_tarski @ X0))
% 1.18/1.38          | (r2_hidden @ (sk_C_1 @ sk_A @ X0) @ sk_B_2))),
% 1.18/1.38      inference('sup-', [status(thm)], ['0', '3'])).
% 1.18/1.38  thf(d1_xboole_0, axiom,
% 1.18/1.38    (![A:$i]:
% 1.18/1.38     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.18/1.38  thf('5', plain,
% 1.18/1.38      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.38  thf('6', plain,
% 1.18/1.38      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.18/1.38      inference('sup-', [status(thm)], ['1', '2'])).
% 1.18/1.38  thf('7', plain,
% 1.18/1.38      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_2))),
% 1.18/1.38      inference('sup-', [status(thm)], ['5', '6'])).
% 1.18/1.38  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('9', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 1.18/1.38      inference('clc', [status(thm)], ['7', '8'])).
% 1.18/1.38  thf(d1_tex_2, axiom,
% 1.18/1.38    (![A:$i]:
% 1.18/1.38     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.18/1.38       ( ( v1_zfmisc_1 @ A ) <=>
% 1.18/1.38         ( ?[B:$i]:
% 1.18/1.38           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 1.18/1.38  thf('10', plain,
% 1.18/1.38      (![X42 : $i]:
% 1.18/1.38         (~ (v1_zfmisc_1 @ X42)
% 1.18/1.38          | ((X42) = (k6_domain_1 @ X42 @ (sk_B_1 @ X42)))
% 1.18/1.38          | (v1_xboole_0 @ X42))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.18/1.38  thf('11', plain,
% 1.18/1.38      (![X42 : $i]:
% 1.18/1.38         (~ (v1_zfmisc_1 @ X42)
% 1.18/1.38          | (m1_subset_1 @ (sk_B_1 @ X42) @ X42)
% 1.18/1.38          | (v1_xboole_0 @ X42))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.18/1.38  thf(redefinition_k6_domain_1, axiom,
% 1.18/1.38    (![A:$i,B:$i]:
% 1.18/1.38     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.18/1.38       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.18/1.38  thf('12', plain,
% 1.18/1.38      (![X40 : $i, X41 : $i]:
% 1.18/1.38         ((v1_xboole_0 @ X40)
% 1.18/1.38          | ~ (m1_subset_1 @ X41 @ X40)
% 1.18/1.38          | ((k6_domain_1 @ X40 @ X41) = (k1_tarski @ X41)))),
% 1.18/1.38      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.18/1.38  thf('13', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         ((v1_xboole_0 @ X0)
% 1.18/1.38          | ~ (v1_zfmisc_1 @ X0)
% 1.18/1.38          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.18/1.38          | (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['11', '12'])).
% 1.18/1.38  thf('14', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.18/1.38          | ~ (v1_zfmisc_1 @ X0)
% 1.18/1.38          | (v1_xboole_0 @ X0))),
% 1.18/1.38      inference('simplify', [status(thm)], ['13'])).
% 1.18/1.38  thf('15', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.18/1.38          | (v1_xboole_0 @ X0)
% 1.18/1.38          | ~ (v1_zfmisc_1 @ X0)
% 1.18/1.38          | (v1_xboole_0 @ X0)
% 1.18/1.38          | ~ (v1_zfmisc_1 @ X0))),
% 1.18/1.38      inference('sup+', [status(thm)], ['10', '14'])).
% 1.18/1.38  thf('16', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (~ (v1_zfmisc_1 @ X0)
% 1.18/1.38          | (v1_xboole_0 @ X0)
% 1.18/1.38          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 1.18/1.38      inference('simplify', [status(thm)], ['15'])).
% 1.18/1.38  thf('17', plain,
% 1.18/1.38      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X17 @ X16)
% 1.18/1.38          | ((X17) = (X14))
% 1.18/1.38          | ((X16) != (k1_tarski @ X14)))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_tarski])).
% 1.18/1.38  thf('18', plain,
% 1.18/1.38      (![X14 : $i, X17 : $i]:
% 1.18/1.38         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 1.18/1.38      inference('simplify', [status(thm)], ['17'])).
% 1.18/1.38  thf('19', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X1 @ X0)
% 1.18/1.38          | (v1_xboole_0 @ X0)
% 1.18/1.38          | ~ (v1_zfmisc_1 @ X0)
% 1.18/1.38          | ((X1) = (sk_B_1 @ X0)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['16', '18'])).
% 1.18/1.38  thf('20', plain,
% 1.18/1.38      ((((sk_B @ sk_A) = (sk_B_1 @ sk_B_2))
% 1.18/1.38        | ~ (v1_zfmisc_1 @ sk_B_2)
% 1.18/1.38        | (v1_xboole_0 @ sk_B_2))),
% 1.18/1.38      inference('sup-', [status(thm)], ['9', '19'])).
% 1.18/1.38  thf('21', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('22', plain,
% 1.18/1.38      ((((sk_B @ sk_A) = (sk_B_1 @ sk_B_2)) | (v1_xboole_0 @ sk_B_2))),
% 1.18/1.38      inference('demod', [status(thm)], ['20', '21'])).
% 1.18/1.38  thf('23', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('24', plain, (((sk_B @ sk_A) = (sk_B_1 @ sk_B_2))),
% 1.18/1.38      inference('clc', [status(thm)], ['22', '23'])).
% 1.18/1.38  thf('25', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (~ (v1_zfmisc_1 @ X0)
% 1.18/1.38          | (v1_xboole_0 @ X0)
% 1.18/1.38          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 1.18/1.38      inference('simplify', [status(thm)], ['15'])).
% 1.18/1.38  thf('26', plain,
% 1.18/1.38      ((((sk_B_2) = (k1_tarski @ (sk_B @ sk_A)))
% 1.18/1.38        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.38        | ~ (v1_zfmisc_1 @ sk_B_2))),
% 1.18/1.38      inference('sup+', [status(thm)], ['24', '25'])).
% 1.18/1.38  thf('27', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('28', plain,
% 1.18/1.38      ((((sk_B_2) = (k1_tarski @ (sk_B @ sk_A))) | (v1_xboole_0 @ sk_B_2))),
% 1.18/1.38      inference('demod', [status(thm)], ['26', '27'])).
% 1.18/1.38  thf('29', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('30', plain, (((sk_B_2) = (k1_tarski @ (sk_B @ sk_A)))),
% 1.18/1.38      inference('clc', [status(thm)], ['28', '29'])).
% 1.18/1.38  thf('31', plain,
% 1.18/1.38      (![X14 : $i, X17 : $i]:
% 1.18/1.38         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 1.18/1.38      inference('simplify', [status(thm)], ['17'])).
% 1.18/1.38  thf('32', plain,
% 1.18/1.38      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_2) | ((X0) = (sk_B @ sk_A)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['30', '31'])).
% 1.18/1.38  thf('33', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (((sk_A) = (k1_tarski @ X0))
% 1.18/1.38          | ((sk_C_1 @ sk_A @ X0) = (X0))
% 1.18/1.38          | ((sk_C_1 @ sk_A @ X0) = (sk_B @ sk_A)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['4', '32'])).
% 1.18/1.38  thf('34', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (((sk_B @ sk_A) != (X0))
% 1.18/1.38          | ((sk_C_1 @ sk_A @ X0) = (X0))
% 1.18/1.38          | ((sk_A) = (k1_tarski @ X0)))),
% 1.18/1.38      inference('eq_fact', [status(thm)], ['33'])).
% 1.18/1.38  thf('35', plain,
% 1.18/1.38      ((((sk_A) = (k1_tarski @ (sk_B @ sk_A)))
% 1.18/1.38        | ((sk_C_1 @ sk_A @ (sk_B @ sk_A)) = (sk_B @ sk_A)))),
% 1.18/1.38      inference('simplify', [status(thm)], ['34'])).
% 1.18/1.38  thf('36', plain, (((sk_B_2) = (k1_tarski @ (sk_B @ sk_A)))),
% 1.18/1.38      inference('clc', [status(thm)], ['28', '29'])).
% 1.18/1.38  thf('37', plain,
% 1.18/1.38      ((((sk_A) = (sk_B_2)) | ((sk_C_1 @ sk_A @ (sk_B @ sk_A)) = (sk_B @ sk_A)))),
% 1.18/1.38      inference('demod', [status(thm)], ['35', '36'])).
% 1.18/1.38  thf('38', plain, (((sk_A) != (sk_B_2))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('39', plain, (((sk_C_1 @ sk_A @ (sk_B @ sk_A)) = (sk_B @ sk_A))),
% 1.18/1.38      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 1.18/1.38  thf('40', plain,
% 1.18/1.38      (![X14 : $i, X18 : $i]:
% 1.18/1.38         (((X18) = (k1_tarski @ X14))
% 1.18/1.38          | ((sk_C_1 @ X18 @ X14) != (X14))
% 1.18/1.38          | ~ (r2_hidden @ (sk_C_1 @ X18 @ X14) @ X18))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_tarski])).
% 1.18/1.38  thf('41', plain,
% 1.18/1.38      ((~ (r2_hidden @ (sk_B @ sk_A) @ sk_A)
% 1.18/1.38        | ((sk_C_1 @ sk_A @ (sk_B @ sk_A)) != (sk_B @ sk_A))
% 1.18/1.38        | ((sk_A) = (k1_tarski @ (sk_B @ sk_A))))),
% 1.18/1.38      inference('sup-', [status(thm)], ['39', '40'])).
% 1.18/1.38  thf('42', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 1.18/1.38      inference('clc', [status(thm)], ['7', '8'])).
% 1.18/1.38  thf('43', plain, (((sk_B_2) = (k1_tarski @ (sk_B @ sk_A)))),
% 1.18/1.38      inference('clc', [status(thm)], ['28', '29'])).
% 1.18/1.38  thf('44', plain,
% 1.18/1.38      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.38  thf('45', plain,
% 1.18/1.38      (![X4 : $i, X6 : $i]:
% 1.18/1.38         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.18/1.38      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.38  thf('46', plain,
% 1.18/1.38      (![X14 : $i, X17 : $i]:
% 1.18/1.38         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 1.18/1.38      inference('simplify', [status(thm)], ['17'])).
% 1.18/1.38  thf('47', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.18/1.38          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.18/1.38      inference('sup-', [status(thm)], ['45', '46'])).
% 1.18/1.38  thf('48', plain,
% 1.18/1.38      (![X4 : $i, X6 : $i]:
% 1.18/1.38         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.18/1.38      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.38  thf('49', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X0 @ X1)
% 1.18/1.38          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.18/1.38          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.18/1.38      inference('sup-', [status(thm)], ['47', '48'])).
% 1.18/1.38  thf('50', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.18/1.38      inference('simplify', [status(thm)], ['49'])).
% 1.18/1.38  thf('51', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['44', '50'])).
% 1.18/1.38  thf('52', plain, (((r1_tarski @ sk_B_2 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 1.18/1.38      inference('sup+', [status(thm)], ['43', '51'])).
% 1.18/1.38  thf('53', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('54', plain, ((r1_tarski @ sk_B_2 @ sk_A)),
% 1.18/1.38      inference('clc', [status(thm)], ['52', '53'])).
% 1.18/1.38  thf('55', plain,
% 1.18/1.38      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X3 @ X4)
% 1.18/1.38          | (r2_hidden @ X3 @ X5)
% 1.18/1.38          | ~ (r1_tarski @ X4 @ X5))),
% 1.18/1.38      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.38  thf('56', plain,
% 1.18/1.38      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 1.18/1.38      inference('sup-', [status(thm)], ['54', '55'])).
% 1.18/1.38  thf('57', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 1.18/1.38      inference('sup-', [status(thm)], ['42', '56'])).
% 1.18/1.38  thf('58', plain, (((sk_C_1 @ sk_A @ (sk_B @ sk_A)) = (sk_B @ sk_A))),
% 1.18/1.38      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 1.18/1.38  thf('59', plain, (((sk_B_2) = (k1_tarski @ (sk_B @ sk_A)))),
% 1.18/1.38      inference('clc', [status(thm)], ['28', '29'])).
% 1.18/1.38  thf('60', plain, ((((sk_B @ sk_A) != (sk_B @ sk_A)) | ((sk_A) = (sk_B_2)))),
% 1.18/1.38      inference('demod', [status(thm)], ['41', '57', '58', '59'])).
% 1.18/1.38  thf('61', plain, (((sk_A) = (sk_B_2))),
% 1.18/1.38      inference('simplify', [status(thm)], ['60'])).
% 1.18/1.38  thf('62', plain, (((sk_A) != (sk_B_2))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('63', plain, ($false),
% 1.18/1.38      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 1.18/1.38  
% 1.18/1.38  % SZS output end Refutation
% 1.18/1.38  
% 1.18/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
