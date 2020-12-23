%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tW5MA5dIun

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 102 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  386 ( 985 expanded)
%              Number of equality atoms :   39 (  86 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v3_relat_2_type,type,(
    v3_relat_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( v1_partfun1 @ X10 @ X11 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_3 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_xboole_0 @ sk_B_3 ),
    inference(clc,[status(thm)],['5','6'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_B_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B_3 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B_3 != k1_xboole_0 )
   <= ( sk_B_3 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('15',plain,(
    ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3 ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('24',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','24','25'])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(rc2_partfun1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_partfun1 @ B @ A )
      & ( v8_relat_2 @ B )
      & ( v4_relat_2 @ B )
      & ( v3_relat_2 @ B )
      & ( v1_relat_2 @ B )
      & ( v5_relat_1 @ B @ A )
      & ( v4_relat_1 @ B @ A )
      & ( v1_relat_1 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) )).

thf('31',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_2 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[rc2_partfun1])).

thf('32',plain,(
    m1_subset_1 @ ( sk_B_2 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_2 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_2 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,(
    ! [X13: $i] :
      ( v1_partfun1 @ ( sk_B_2 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[rc2_partfun1])).

thf('39',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','27','39'])).

thf('41',plain,
    ( ( sk_B_3 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('42',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['13','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tW5MA5dIun
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 60 iterations in 0.011s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.20/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.20/0.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.45  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.45  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.20/0.45  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.45  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.20/0.45  thf(v3_relat_2_type, type, v3_relat_2: $i > $o).
% 0.20/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(t132_funct_2, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.45           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.45           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.45        ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.45            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45          ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.45              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.45              ( v1_partfun1 @ C @ A ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t132_funct_2])).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(cc5_funct_2, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.45       ( ![C:$i]:
% 0.20/0.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.45           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.45             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.20/0.45          | (v1_partfun1 @ X10 @ X11)
% 0.20/0.45          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.20/0.45          | ~ (v1_funct_1 @ X10)
% 0.20/0.45          | (v1_xboole_0 @ X12))),
% 0.20/0.45      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (((v1_xboole_0 @ sk_B_3)
% 0.20/0.45        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.45        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_3)
% 0.20/0.45        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf('3', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('4', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_3)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('5', plain, (((v1_xboole_0 @ sk_B_3) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.45  thf('6', plain, (~ (v1_partfun1 @ sk_C @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('7', plain, ((v1_xboole_0 @ sk_B_3)),
% 0.20/0.45      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.45  thf(t7_xboole_0, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.45          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.45  thf(d1_xboole_0, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('11', plain, (((sk_B_3) = (k1_xboole_0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.45  thf('12', plain, ((((sk_B_3) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      ((((sk_B_3) != (k1_xboole_0))) <= (~ (((sk_B_3) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['12'])).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['12'])).
% 0.20/0.45  thf('15', plain, (~ (v1_partfun1 @ sk_C @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      ((~ (v1_partfun1 @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.45  thf('17', plain,
% 0.20/0.45      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.45  thf('18', plain,
% 0.20/0.45      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['12'])).
% 0.20/0.45  thf('19', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('20', plain,
% 0.20/0.45      (((m1_subset_1 @ sk_C @ 
% 0.20/0.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3))))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.45  thf(t5_subset, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.45          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.45          | ~ (v1_xboole_0 @ X9)
% 0.20/0.45          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.45  thf('22', plain,
% 0.20/0.45      ((![X0 : $i]:
% 0.20/0.45          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3))
% 0.20/0.45           | ~ (r2_hidden @ X0 @ sk_C)))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.45  thf(t113_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      (![X5 : $i, X6 : $i]:
% 0.20/0.45         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.45  thf('24', plain,
% 0.20/0.45      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.45  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.45  thf('26', plain,
% 0.20/0.45      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('demod', [status(thm)], ['22', '24', '25'])).
% 0.20/0.45  thf('27', plain,
% 0.20/0.45      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['17', '26'])).
% 0.20/0.45  thf('28', plain,
% 0.20/0.45      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.45  thf('29', plain,
% 0.20/0.45      (![X5 : $i, X6 : $i]:
% 0.20/0.45         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.45  thf('30', plain,
% 0.20/0.45      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.45  thf(rc2_partfun1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ?[B:$i]:
% 0.20/0.45       ( ( v1_partfun1 @ B @ A ) & ( v8_relat_2 @ B ) & ( v4_relat_2 @ B ) & 
% 0.20/0.45         ( v3_relat_2 @ B ) & ( v1_relat_2 @ B ) & ( v5_relat_1 @ B @ A ) & 
% 0.20/0.45         ( v4_relat_1 @ B @ A ) & ( v1_relat_1 @ B ) & 
% 0.20/0.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.20/0.45  thf('31', plain,
% 0.20/0.45      (![X13 : $i]:
% 0.20/0.45         (m1_subset_1 @ (sk_B_2 @ X13) @ 
% 0.20/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 0.20/0.45      inference('cnf', [status(esa)], [rc2_partfun1])).
% 0.20/0.45  thf('32', plain,
% 0.20/0.45      ((m1_subset_1 @ (sk_B_2 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.45      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.45  thf('33', plain,
% 0.20/0.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.45          | ~ (v1_xboole_0 @ X9)
% 0.20/0.45          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.45  thf('34', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.45          | ~ (r2_hidden @ X0 @ (sk_B_2 @ k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.45  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.45  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_2 @ k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.45  thf('37', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['28', '36'])).
% 0.20/0.45  thf('38', plain, (![X13 : $i]: (v1_partfun1 @ (sk_B_2 @ X13) @ X13)),
% 0.20/0.45      inference('cnf', [status(esa)], [rc2_partfun1])).
% 0.20/0.45  thf('39', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.45      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.45  thf('40', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.45      inference('demod', [status(thm)], ['16', '27', '39'])).
% 0.20/0.45  thf('41', plain,
% 0.20/0.45      (~ (((sk_B_3) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.20/0.45      inference('split', [status(esa)], ['12'])).
% 0.20/0.45  thf('42', plain, (~ (((sk_B_3) = (k1_xboole_0)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.20/0.45  thf('43', plain, (((sk_B_3) != (k1_xboole_0))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['13', '42'])).
% 0.20/0.45  thf('44', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['11', '43'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
