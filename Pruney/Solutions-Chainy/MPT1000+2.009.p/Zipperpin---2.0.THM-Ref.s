%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jwQoqGlCb2

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:58 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 109 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  506 (1329 expanded)
%              Number of equality atoms :   67 ( 173 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k8_relset_1 @ A @ B @ C @ B )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('3',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relset_1 @ X0 @ X1 @ X2 @ X1 )
        = ( k1_relset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('11',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_A ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','12'])).

thf('14',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X3: $i] :
      ( zip_tseitin_0 @ X3 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','28'])).

thf('30',plain,
    ( ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('32',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B )
     != sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('35',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relset_1 @ X0 @ X1 @ X2 @ X1 )
        = ( k1_relset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('38',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B )
      = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['30','39'])).

thf('41',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jwQoqGlCb2
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.55  % Solved by: fo/fo7.sh
% 0.39/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.55  % done 77 iterations in 0.091s
% 0.39/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.55  % SZS output start Refutation
% 0.39/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.55  thf(d1_funct_2, axiom,
% 0.39/0.55    (![A:$i,B:$i,C:$i]:
% 0.39/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.55  thf(zf_stmt_0, axiom,
% 0.39/0.55    (![B:$i,A:$i]:
% 0.39/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.55       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.55  thf('0', plain,
% 0.39/0.55      (![X3 : $i, X4 : $i]:
% 0.39/0.55         ((zip_tseitin_0 @ X3 @ X4) | ((X3) = (k1_xboole_0)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf(t48_funct_2, conjecture,
% 0.39/0.55    (![A:$i,B:$i,C:$i]:
% 0.39/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.55         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.39/0.55  thf(zf_stmt_1, negated_conjecture,
% 0.39/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.55          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.55            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ) )),
% 0.39/0.55    inference('cnf.neg', [status(esa)], [t48_funct_2])).
% 0.39/0.55  thf('1', plain,
% 0.39/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.55  thf(zf_stmt_3, axiom,
% 0.39/0.55    (![C:$i,B:$i,A:$i]:
% 0.39/0.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.55  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.55  thf(zf_stmt_5, axiom,
% 0.39/0.55    (![A:$i,B:$i,C:$i]:
% 0.39/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.55  thf('2', plain,
% 0.39/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.55         (~ (zip_tseitin_0 @ X8 @ X9)
% 0.39/0.55          | (zip_tseitin_1 @ X10 @ X8 @ X9)
% 0.39/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8))))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.55  thf('3', plain,
% 0.39/0.55      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.39/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.55  thf('4', plain,
% 0.39/0.55      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.39/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.39/0.55  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('6', plain,
% 0.39/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.55         (~ (v1_funct_2 @ X7 @ X5 @ X6)
% 0.39/0.55          | ((X5) = (k1_relset_1 @ X5 @ X6 @ X7))
% 0.39/0.55          | ~ (zip_tseitin_1 @ X7 @ X6 @ X5))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.55  thf('7', plain,
% 0.39/0.55      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.39/0.55        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.55  thf('8', plain, (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (sk_A))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('9', plain,
% 0.39/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf(t38_relset_1, axiom,
% 0.39/0.55    (![A:$i,B:$i,C:$i]:
% 0.39/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.55       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.39/0.55         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.55  thf('10', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.55         (((k8_relset_1 @ X0 @ X1 @ X2 @ X1) = (k1_relset_1 @ X0 @ X1 @ X2))
% 0.39/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.39/0.55      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.39/0.55  thf('11', plain,
% 0.39/0.55      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.55         = (k1_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.55  thf('12', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_A))),
% 0.39/0.55      inference('demod', [status(thm)], ['8', '11'])).
% 0.39/0.55  thf('13', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.39/0.55      inference('simplify_reflect-', [status(thm)], ['7', '12'])).
% 0.39/0.55  thf('14', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['4', '13'])).
% 0.39/0.55  thf('15', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('16', plain,
% 0.39/0.55      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.39/0.55      inference('split', [status(esa)], ['15'])).
% 0.39/0.55  thf('17', plain,
% 0.39/0.55      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('split', [status(esa)], ['15'])).
% 0.39/0.55  thf('18', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('19', plain,
% 0.39/0.55      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.55  thf('20', plain,
% 0.39/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.55         (~ (v1_funct_2 @ X7 @ X5 @ X6)
% 0.39/0.55          | ((X5) = (k1_relset_1 @ X5 @ X6 @ X7))
% 0.39/0.55          | ~ (zip_tseitin_1 @ X7 @ X6 @ X5))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.55  thf('21', plain,
% 0.39/0.55      (((~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.39/0.55         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C))))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.55  thf('22', plain,
% 0.39/0.55      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('split', [status(esa)], ['15'])).
% 0.39/0.55  thf('23', plain,
% 0.39/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('24', plain,
% 0.39/0.55      (((m1_subset_1 @ sk_C @ 
% 0.39/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.55  thf('25', plain,
% 0.39/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.55         (~ (zip_tseitin_0 @ X8 @ X9)
% 0.39/0.55          | (zip_tseitin_1 @ X10 @ X8 @ X9)
% 0.39/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8))))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.55  thf('26', plain,
% 0.39/0.55      ((((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0)
% 0.39/0.55         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.55  thf('27', plain,
% 0.39/0.55      (![X3 : $i, X4 : $i]:
% 0.39/0.55         ((zip_tseitin_0 @ X3 @ X4) | ((X4) != (k1_xboole_0)))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('28', plain, (![X3 : $i]: (zip_tseitin_0 @ X3 @ k1_xboole_0)),
% 0.39/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.39/0.55  thf('29', plain,
% 0.39/0.55      (((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('demod', [status(thm)], ['26', '28'])).
% 0.39/0.55  thf('30', plain,
% 0.39/0.55      ((((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C)))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('demod', [status(thm)], ['21', '29'])).
% 0.39/0.55  thf('31', plain,
% 0.39/0.55      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('split', [status(esa)], ['15'])).
% 0.39/0.55  thf('32', plain, (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (sk_A))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.55  thf('33', plain,
% 0.39/0.55      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B) != (sk_A)))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.55  thf('34', plain,
% 0.39/0.55      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('split', [status(esa)], ['15'])).
% 0.39/0.55  thf('35', plain,
% 0.39/0.55      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B) != (k1_xboole_0)))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.55  thf('36', plain,
% 0.39/0.55      (((m1_subset_1 @ sk_C @ 
% 0.39/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.55  thf('37', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.55         (((k8_relset_1 @ X0 @ X1 @ X2 @ X1) = (k1_relset_1 @ X0 @ X1 @ X2))
% 0.39/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.39/0.55      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.39/0.55  thf('38', plain,
% 0.39/0.55      ((((k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_B)
% 0.39/0.55          = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C)))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.55  thf('39', plain,
% 0.39/0.55      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C) != (k1_xboole_0)))
% 0.39/0.55         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.55      inference('demod', [status(thm)], ['35', '38'])).
% 0.39/0.55  thf('40', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.39/0.55      inference('simplify_reflect-', [status(thm)], ['30', '39'])).
% 0.39/0.55  thf('41', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.39/0.55      inference('split', [status(esa)], ['15'])).
% 0.39/0.55  thf('42', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.39/0.55      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.39/0.55  thf('43', plain, (((sk_B) != (k1_xboole_0))),
% 0.39/0.55      inference('simpl_trail', [status(thm)], ['16', '42'])).
% 0.39/0.55  thf('44', plain, ($false),
% 0.39/0.55      inference('simplify_reflect-', [status(thm)], ['14', '43'])).
% 0.39/0.55  
% 0.39/0.55  % SZS output end Refutation
% 0.39/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
