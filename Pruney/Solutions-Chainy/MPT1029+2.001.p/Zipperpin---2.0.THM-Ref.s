%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oZxFDi6C3Y

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:01 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 102 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  391 (1029 expanded)
%              Number of equality atoms :   45 ( 104 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t132_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( v1_partfun1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_2 @ sk_B_4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X81: $i,X82: $i,X83: $i] :
      ( ~ ( m1_subset_1 @ X81 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X82 @ X83 ) ) )
      | ( v1_partfun1 @ X81 @ X82 )
      | ~ ( v1_funct_2 @ X81 @ X82 @ X83 )
      | ~ ( v1_funct_1 @ X81 )
      | ( v1_xboole_0 @ X83 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_B_4 )
    | ~ ( v1_funct_1 @ sk_C_5 )
    | ~ ( v1_funct_2 @ sk_C_5 @ sk_A_2 @ sk_B_4 )
    | ( v1_partfun1 @ sk_C_5 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_C_5 @ sk_A_2 @ sk_B_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_B_4 )
    | ( v1_partfun1 @ sk_C_5 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v1_partfun1 @ sk_C_5 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_xboole_0 @ sk_B_4 ),
    inference(clc,[status(thm)],['5','6'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('9',plain,(
    sk_B_4 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B_4 != k1_xboole_0 )
    | ( sk_A_2 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_B_4 != k1_xboole_0 )
   <= ( sk_B_4 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('14',plain,(
    ! [X85: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X85 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X85 @ X85 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('15',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('16',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('17',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X84: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X84 ) @ X84 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A_2 = k1_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('29',plain,(
    ~ ( v1_partfun1 @ sk_C_5 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_partfun1 @ sk_C_5 @ k1_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A_2 = k1_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_2 @ sk_B_4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_4 ) ) )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,
    ( ( r1_tarski @ sk_C_5 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_4 ) )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('37',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( r1_tarski @ sk_C_5 @ k1_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('40',plain,
    ( ( sk_C_5 = k1_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','40'])).

thf('42',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,
    ( ( sk_B_4 != k1_xboole_0 )
    | ( sk_A_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('44',plain,(
    sk_B_4 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_B_4 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['11','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oZxFDi6C3Y
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.66  % Solved by: fo/fo7.sh
% 0.48/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.66  % done 347 iterations in 0.209s
% 0.48/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.66  % SZS output start Refutation
% 0.48/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.48/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.48/0.66  thf(sk_A_2_type, type, sk_A_2: $i).
% 0.48/0.66  thf(sk_B_4_type, type, sk_B_4: $i).
% 0.48/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.66  thf(sk_C_5_type, type, sk_C_5: $i).
% 0.48/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.66  thf(t132_funct_2, conjecture,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( ( v1_funct_1 @ C ) & 
% 0.48/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.66       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.48/0.66           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.48/0.66           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.48/0.66        ( ( ( v1_funct_1 @ C ) & 
% 0.48/0.66            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.66          ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.48/0.66              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.66            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.48/0.66              ( v1_partfun1 @ C @ A ) ) ) ) )),
% 0.48/0.66    inference('cnf.neg', [status(esa)], [t132_funct_2])).
% 0.48/0.66  thf('0', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_2 @ sk_B_4)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(cc5_funct_2, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.48/0.66       ( ![C:$i]:
% 0.48/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.48/0.66             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.48/0.66  thf('1', plain,
% 0.48/0.66      (![X81 : $i, X82 : $i, X83 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X81 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X82 @ X83)))
% 0.48/0.66          | (v1_partfun1 @ X81 @ X82)
% 0.48/0.66          | ~ (v1_funct_2 @ X81 @ X82 @ X83)
% 0.48/0.66          | ~ (v1_funct_1 @ X81)
% 0.48/0.66          | (v1_xboole_0 @ X83))),
% 0.48/0.66      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.48/0.66  thf('2', plain,
% 0.48/0.66      (((v1_xboole_0 @ sk_B_4)
% 0.48/0.66        | ~ (v1_funct_1 @ sk_C_5)
% 0.48/0.66        | ~ (v1_funct_2 @ sk_C_5 @ sk_A_2 @ sk_B_4)
% 0.48/0.66        | (v1_partfun1 @ sk_C_5 @ sk_A_2))),
% 0.48/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.48/0.66  thf('3', plain, ((v1_funct_1 @ sk_C_5)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('4', plain, ((v1_funct_2 @ sk_C_5 @ sk_A_2 @ sk_B_4)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('5', plain, (((v1_xboole_0 @ sk_B_4) | (v1_partfun1 @ sk_C_5 @ sk_A_2))),
% 0.48/0.66      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.48/0.66  thf('6', plain, (~ (v1_partfun1 @ sk_C_5 @ sk_A_2)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('7', plain, ((v1_xboole_0 @ sk_B_4)),
% 0.48/0.66      inference('clc', [status(thm)], ['5', '6'])).
% 0.48/0.66  thf(t6_boole, axiom,
% 0.48/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.66  thf('8', plain,
% 0.48/0.66      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 0.48/0.66      inference('cnf', [status(esa)], [t6_boole])).
% 0.48/0.66  thf('9', plain, (((sk_B_4) = (k1_xboole_0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.66  thf('10', plain,
% 0.48/0.66      ((((sk_B_4) != (k1_xboole_0)) | ((sk_A_2) = (k1_xboole_0)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('11', plain,
% 0.48/0.66      ((((sk_B_4) != (k1_xboole_0))) <= (~ (((sk_B_4) = (k1_xboole_0))))),
% 0.48/0.66      inference('split', [status(esa)], ['10'])).
% 0.48/0.66  thf(t113_zfmisc_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.48/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.48/0.66  thf('12', plain,
% 0.48/0.66      (![X8 : $i, X9 : $i]:
% 0.48/0.66         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.48/0.66  thf('13', plain,
% 0.48/0.66      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.66      inference('simplify', [status(thm)], ['12'])).
% 0.48/0.66  thf(dt_k6_partfun1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( m1_subset_1 @
% 0.48/0.66         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.48/0.66       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.48/0.66  thf('14', plain,
% 0.48/0.66      (![X85 : $i]:
% 0.48/0.66         (m1_subset_1 @ (k6_partfun1 @ X85) @ 
% 0.48/0.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X85 @ X85)))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.48/0.66  thf('15', plain,
% 0.48/0.66      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.48/0.66      inference('sup+', [status(thm)], ['13', '14'])).
% 0.48/0.66  thf(t1_zfmisc_1, axiom,
% 0.48/0.66    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.48/0.66  thf('16', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.48/0.66      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.48/0.66  thf('17', plain,
% 0.48/0.66      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_tarski @ k1_xboole_0))),
% 0.48/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.48/0.66  thf('18', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.48/0.66      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.48/0.66  thf(t3_subset, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.66  thf('19', plain,
% 0.48/0.66      (![X25 : $i, X26 : $i]:
% 0.48/0.66         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.66  thf('20', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X0 @ (k1_tarski @ k1_xboole_0))
% 0.48/0.66          | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.66  thf('21', plain, ((r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.48/0.66      inference('sup-', [status(thm)], ['17', '20'])).
% 0.48/0.66  thf('22', plain,
% 0.48/0.66      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.66      inference('simplify', [status(thm)], ['12'])).
% 0.48/0.66  thf(t135_zfmisc_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.48/0.66         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.48/0.66       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.66  thf('23', plain,
% 0.48/0.66      (![X10 : $i, X11 : $i]:
% 0.48/0.66         (((X10) = (k1_xboole_0))
% 0.48/0.66          | ~ (r1_tarski @ X10 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.48/0.66  thf('24', plain,
% 0.48/0.66      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.48/0.66  thf('25', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['21', '24'])).
% 0.48/0.66  thf('26', plain, (![X84 : $i]: (v1_partfun1 @ (k6_partfun1 @ X84) @ X84)),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.48/0.66  thf('27', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.48/0.66      inference('sup+', [status(thm)], ['25', '26'])).
% 0.48/0.66  thf('28', plain,
% 0.48/0.66      ((((sk_A_2) = (k1_xboole_0))) <= ((((sk_A_2) = (k1_xboole_0))))),
% 0.48/0.66      inference('split', [status(esa)], ['10'])).
% 0.48/0.66  thf('29', plain, (~ (v1_partfun1 @ sk_C_5 @ sk_A_2)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('30', plain,
% 0.48/0.66      ((~ (v1_partfun1 @ sk_C_5 @ k1_xboole_0))
% 0.48/0.66         <= ((((sk_A_2) = (k1_xboole_0))))),
% 0.48/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.48/0.66  thf('31', plain,
% 0.48/0.66      ((((sk_A_2) = (k1_xboole_0))) <= ((((sk_A_2) = (k1_xboole_0))))),
% 0.48/0.66      inference('split', [status(esa)], ['10'])).
% 0.48/0.66  thf('32', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_2 @ sk_B_4)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('33', plain,
% 0.48/0.66      (((m1_subset_1 @ sk_C_5 @ 
% 0.48/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_4))))
% 0.48/0.66         <= ((((sk_A_2) = (k1_xboole_0))))),
% 0.48/0.66      inference('sup+', [status(thm)], ['31', '32'])).
% 0.48/0.66  thf('34', plain,
% 0.48/0.66      (![X25 : $i, X26 : $i]:
% 0.48/0.66         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.66  thf('35', plain,
% 0.48/0.66      (((r1_tarski @ sk_C_5 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_4)))
% 0.48/0.66         <= ((((sk_A_2) = (k1_xboole_0))))),
% 0.48/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.66  thf('36', plain,
% 0.48/0.66      (![X8 : $i, X9 : $i]:
% 0.48/0.66         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.48/0.66  thf('37', plain,
% 0.48/0.66      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.48/0.66      inference('simplify', [status(thm)], ['36'])).
% 0.48/0.66  thf('38', plain,
% 0.48/0.66      (((r1_tarski @ sk_C_5 @ k1_xboole_0)) <= ((((sk_A_2) = (k1_xboole_0))))),
% 0.48/0.66      inference('demod', [status(thm)], ['35', '37'])).
% 0.48/0.66  thf('39', plain,
% 0.48/0.66      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.48/0.66  thf('40', plain,
% 0.48/0.66      ((((sk_C_5) = (k1_xboole_0))) <= ((((sk_A_2) = (k1_xboole_0))))),
% 0.48/0.66      inference('sup-', [status(thm)], ['38', '39'])).
% 0.48/0.66  thf('41', plain,
% 0.48/0.66      ((~ (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0))
% 0.48/0.66         <= ((((sk_A_2) = (k1_xboole_0))))),
% 0.48/0.66      inference('demod', [status(thm)], ['30', '40'])).
% 0.48/0.66  thf('42', plain, (~ (((sk_A_2) = (k1_xboole_0)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['27', '41'])).
% 0.48/0.66  thf('43', plain,
% 0.48/0.66      (~ (((sk_B_4) = (k1_xboole_0))) | (((sk_A_2) = (k1_xboole_0)))),
% 0.48/0.66      inference('split', [status(esa)], ['10'])).
% 0.48/0.66  thf('44', plain, (~ (((sk_B_4) = (k1_xboole_0)))),
% 0.48/0.66      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 0.48/0.66  thf('45', plain, (((sk_B_4) != (k1_xboole_0))),
% 0.48/0.66      inference('simpl_trail', [status(thm)], ['11', '44'])).
% 0.48/0.66  thf('46', plain, ($false),
% 0.48/0.66      inference('simplify_reflect-', [status(thm)], ['9', '45'])).
% 0.48/0.66  
% 0.48/0.66  % SZS output end Refutation
% 0.48/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
