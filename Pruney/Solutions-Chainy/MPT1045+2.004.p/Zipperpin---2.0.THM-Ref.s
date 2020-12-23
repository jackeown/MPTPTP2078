%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.woXieaxpmG

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 148 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  538 (2214 expanded)
%              Number of equality atoms :   58 ( 242 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_partfun1_type,type,(
    k3_partfun1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t161_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) )
          = ( k1_tarski @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) )
            = ( k1_tarski @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t161_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t174_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_partfun1 @ C @ A )
      <=> ( ( k5_partfun1 @ A @ B @ C )
          = ( k1_tarski @ C ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_partfun1 @ X3 @ X4 )
      | ( ( k5_partfun1 @ X4 @ X5 @ X3 )
        = ( k1_tarski @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t174_partfun1])).

thf('2',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ( k5_partfun1 @ sk_A @ sk_B @ ( k3_partfun1 @ sk_C @ sk_A @ sk_B ) )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k3_partfun1 @ C @ A @ B )
        = C ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k3_partfun1 @ X6 @ X7 @ X8 )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t87_partfun1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k3_partfun1 @ sk_C @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k3_partfun1 @ sk_C @ sk_A @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
 != ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t133_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( v1_partfun1 @ ( k3_partfun1 @ C @ A @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( v1_partfun1 @ ( k3_partfun1 @ X1 @ X0 @ X2 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t133_funct_2])).

thf('15',plain,
    ( ( v1_partfun1 @ ( k3_partfun1 @ sk_C @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_partfun1 @ sk_C @ sk_A @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_partfun1 @ sk_C @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_partfun1 @ X3 @ X4 )
      | ( ( k5_partfun1 @ X4 @ X5 @ X3 )
        = ( k1_tarski @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t174_partfun1])).

thf('26',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ( ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C )
        = ( k1_tarski @ sk_C ) )
      | ~ ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( v1_partfun1 @ ( k3_partfun1 @ X1 @ X0 @ X2 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t133_funct_2])).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_partfun1 @ ( k3_partfun1 @ X1 @ k1_xboole_0 @ X2 ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X1 @ k1_xboole_0 @ X2 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
      | ( v1_partfun1 @ ( k3_partfun1 @ sk_C @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_partfun1 @ ( k3_partfun1 @ sk_C @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k3_partfun1 @ X6 @ X7 @ X8 )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t87_partfun1])).

thf('39',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ( ( k3_partfun1 @ sk_C @ k1_xboole_0 @ sk_B )
        = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k3_partfun1 @ sk_C @ k1_xboole_0 @ sk_B )
      = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,
    ( ( ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C )
      = ( k1_tarski @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27','42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('45',plain,(
    ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
 != ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('46',plain,
    ( ( ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C )
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('49',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['21','49'])).

thf('51',plain,(
    v1_partfun1 @ sk_C @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['19','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['12','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.woXieaxpmG
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 13:43:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 28 iterations in 0.008s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.45  thf(k3_partfun1_type, type, k3_partfun1: $i > $i > $i > $i).
% 0.20/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.45  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(t161_funct_2, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.45         ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) ) =
% 0.20/0.45           ( k1_tarski @ C ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.45        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.45            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.45            ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) ) =
% 0.20/0.45              ( k1_tarski @ C ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t161_funct_2])).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t174_partfun1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45       ( ( v1_partfun1 @ C @ A ) <=>
% 0.20/0.45         ( ( k5_partfun1 @ A @ B @ C ) = ( k1_tarski @ C ) ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.45         (~ (v1_partfun1 @ X3 @ X4)
% 0.20/0.45          | ((k5_partfun1 @ X4 @ X5 @ X3) = (k1_tarski @ X3))
% 0.20/0.45          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.20/0.45          | ~ (v1_funct_1 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [t174_partfun1])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.45        | ((k5_partfun1 @ sk_A @ sk_B @ sk_C) = (k1_tarski @ sk_C))
% 0.20/0.45        | ~ (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf('3', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      ((((k5_partfun1 @ sk_A @ sk_B @ sk_C) = (k1_tarski @ sk_C))
% 0.20/0.45        | ~ (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (((k5_partfun1 @ sk_A @ sk_B @ (k3_partfun1 @ sk_C @ sk_A @ sk_B))
% 0.20/0.45         != (k1_tarski @ sk_C))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t87_partfun1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45       ( ( k3_partfun1 @ C @ A @ B ) = ( C ) ) ))).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.45         (((k3_partfun1 @ X6 @ X7 @ X8) = (X6))
% 0.20/0.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.20/0.45          | ~ (v1_funct_1 @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t87_partfun1])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      ((~ (v1_funct_1 @ sk_C) | ((k3_partfun1 @ sk_C @ sk_A @ sk_B) = (sk_C)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.45  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('10', plain, (((k3_partfun1 @ sk_C @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (((k5_partfun1 @ sk_A @ sk_B @ sk_C) != (k1_tarski @ sk_C))),
% 0.20/0.45      inference('demod', [status(thm)], ['5', '10'])).
% 0.20/0.45  thf('12', plain, (~ (v1_partfun1 @ sk_C @ sk_A)),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['4', '11'])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t133_funct_2, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.45         ( v1_partfun1 @ ( k3_partfun1 @ C @ A @ B ) @ A ) ) ))).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (((X2) = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_funct_1 @ X1)
% 0.20/0.45          | ~ (v1_funct_2 @ X1 @ X0 @ X2)
% 0.20/0.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.20/0.45          | (v1_partfun1 @ (k3_partfun1 @ X1 @ X0 @ X2) @ X0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t133_funct_2])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (((v1_partfun1 @ (k3_partfun1 @ sk_C @ sk_A @ sk_B) @ sk_A)
% 0.20/0.45        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.45        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.45        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.45  thf('16', plain, (((k3_partfun1 @ sk_C @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('19', plain, (((v1_partfun1 @ sk_C @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.45      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.20/0.45  thf('20', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['20'])).
% 0.20/0.45  thf('22', plain,
% 0.20/0.45      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['20'])).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('24', plain,
% 0.20/0.45      (((m1_subset_1 @ sk_C @ 
% 0.20/0.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.45  thf('25', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.45         (~ (v1_partfun1 @ X3 @ X4)
% 0.20/0.45          | ((k5_partfun1 @ X4 @ X5 @ X3) = (k1_tarski @ X3))
% 0.20/0.45          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.20/0.45          | ~ (v1_funct_1 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [t174_partfun1])).
% 0.20/0.45  thf('26', plain,
% 0.20/0.45      (((~ (v1_funct_1 @ sk_C)
% 0.20/0.45         | ((k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_C))
% 0.20/0.45         | ~ (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.45  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('28', plain,
% 0.20/0.45      (((m1_subset_1 @ sk_C @ 
% 0.20/0.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.45  thf('29', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (((X0) != (k1_xboole_0))
% 0.20/0.45          | ~ (v1_funct_1 @ X1)
% 0.20/0.45          | ~ (v1_funct_2 @ X1 @ X0 @ X2)
% 0.20/0.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.20/0.45          | (v1_partfun1 @ (k3_partfun1 @ X1 @ X0 @ X2) @ X0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t133_funct_2])).
% 0.20/0.45  thf('30', plain,
% 0.20/0.45      (![X1 : $i, X2 : $i]:
% 0.20/0.45         ((v1_partfun1 @ (k3_partfun1 @ X1 @ k1_xboole_0 @ X2) @ k1_xboole_0)
% 0.20/0.45          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.45               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X2)))
% 0.20/0.45          | ~ (v1_funct_2 @ X1 @ k1_xboole_0 @ X2)
% 0.20/0.45          | ~ (v1_funct_1 @ X1))),
% 0.20/0.45      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.45  thf('31', plain,
% 0.20/0.45      (((~ (v1_funct_1 @ sk_C)
% 0.20/0.45         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B)
% 0.20/0.45         | (v1_partfun1 @ (k3_partfun1 @ sk_C @ k1_xboole_0 @ sk_B) @ 
% 0.20/0.45            k1_xboole_0)))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['28', '30'])).
% 0.20/0.45  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('33', plain,
% 0.20/0.45      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['20'])).
% 0.20/0.45  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('35', plain,
% 0.20/0.45      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.45  thf('36', plain,
% 0.20/0.45      (((v1_partfun1 @ (k3_partfun1 @ sk_C @ k1_xboole_0 @ sk_B) @ k1_xboole_0))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.20/0.45  thf('37', plain,
% 0.20/0.45      (((m1_subset_1 @ sk_C @ 
% 0.20/0.45         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.45  thf('38', plain,
% 0.20/0.45      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.45         (((k3_partfun1 @ X6 @ X7 @ X8) = (X6))
% 0.20/0.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.20/0.45          | ~ (v1_funct_1 @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t87_partfun1])).
% 0.20/0.45  thf('39', plain,
% 0.20/0.45      (((~ (v1_funct_1 @ sk_C)
% 0.20/0.45         | ((k3_partfun1 @ sk_C @ k1_xboole_0 @ sk_B) = (sk_C))))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.45  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('41', plain,
% 0.20/0.45      ((((k3_partfun1 @ sk_C @ k1_xboole_0 @ sk_B) = (sk_C)))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.45  thf('42', plain,
% 0.20/0.45      (((v1_partfun1 @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('demod', [status(thm)], ['36', '41'])).
% 0.20/0.45  thf('43', plain,
% 0.20/0.45      ((((k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_C)))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('demod', [status(thm)], ['26', '27', '42'])).
% 0.20/0.45  thf('44', plain,
% 0.20/0.45      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['20'])).
% 0.20/0.45  thf('45', plain,
% 0.20/0.45      (((k5_partfun1 @ sk_A @ sk_B @ sk_C) != (k1_tarski @ sk_C))),
% 0.20/0.45      inference('demod', [status(thm)], ['5', '10'])).
% 0.20/0.45  thf('46', plain,
% 0.20/0.45      ((((k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C) != (k1_tarski @ sk_C)))
% 0.20/0.45         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.45  thf('47', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['43', '46'])).
% 0.20/0.45  thf('48', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.20/0.45      inference('split', [status(esa)], ['20'])).
% 0.20/0.45  thf('49', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.20/0.45  thf('50', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['21', '49'])).
% 0.20/0.45  thf('51', plain, ((v1_partfun1 @ sk_C @ sk_A)),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['19', '50'])).
% 0.20/0.45  thf('52', plain, ($false), inference('demod', [status(thm)], ['12', '51'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
