%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VwkdZmzTdT

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:58 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 222 expanded)
%              Number of leaves         :   29 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  488 (2732 expanded)
%              Number of equality atoms :   38 ( 126 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X14: $i] :
      ( zip_tseitin_0 @ X14 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16
       != ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('20',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['15','18','19'])).

thf('21',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['12','20'])).

thf('22',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['10','21'])).

thf('23',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['6','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','23'])).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( v1_funct_2 @ X21 @ X20 @ X19 )
      | ( X21 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('30',plain,(
    ! [X20: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','28','29'])).

thf('31',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['12','20'])).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['6','22'])).

thf('34',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('42',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['38','39','40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('48',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','48'])).

thf('50',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['24','50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VwkdZmzTdT
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:16:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 145 iterations in 0.124s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.57  thf(l13_xboole_0, axiom,
% 0.37/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.57  thf(d1_funct_2, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, axiom,
% 0.37/0.57    (![B:$i,A:$i]:
% 0.37/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i]:
% 0.37/0.57         ((zip_tseitin_0 @ X14 @ X15) | ((X15) != (k1_xboole_0)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('2', plain, (![X14 : $i]: (zip_tseitin_0 @ X14 @ k1_xboole_0)),
% 0.37/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['0', '2'])).
% 0.37/0.57  thf(t130_funct_2, conjecture,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.57       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.37/0.57         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.57           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_1, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.57        ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.57          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.37/0.57            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.57              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.57  thf(zf_stmt_3, axiom,
% 0.37/0.57    (![C:$i,B:$i,A:$i]:
% 0.37/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.57  thf(zf_stmt_5, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.37/0.57          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.37/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf('7', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.57         (((X16) != (k1_relset_1 @ X16 @ X17 @ X18))
% 0.37/0.57          | (v1_funct_2 @ X18 @ X16 @ X17)
% 0.37/0.57          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      ((((sk_A) != (sk_A))
% 0.37/0.57        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.37/0.57        | (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.37/0.57        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.37/0.57      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.37/0.57        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.37/0.57         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.37/0.57      inference('split', [status(esa)], ['11'])).
% 0.37/0.57  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.57  thf('14', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.37/0.57      inference('split', [status(esa)], ['11'])).
% 0.37/0.57  thf('15', plain, (((v1_funct_1 @ sk_C))),
% 0.37/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= (~
% 0.37/0.57             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('split', [status(esa)], ['11'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.37/0.57       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.37/0.57       ~ ((v1_funct_1 @ sk_C))),
% 0.37/0.57      inference('split', [status(esa)], ['11'])).
% 0.37/0.57  thf('20', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['15', '18', '19'])).
% 0.37/0.57  thf('21', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['12', '20'])).
% 0.37/0.57  thf('22', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.37/0.57      inference('clc', [status(thm)], ['10', '21'])).
% 0.37/0.57  thf('23', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.37/0.57      inference('clc', [status(thm)], ['6', '22'])).
% 0.37/0.57  thf('24', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.57         (((X19) != (k1_xboole_0))
% 0.37/0.57          | ((X20) = (k1_xboole_0))
% 0.37/0.57          | (v1_funct_2 @ X21 @ X20 @ X19)
% 0.37/0.57          | ((X21) != (k1_xboole_0))
% 0.37/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X20 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ k1_xboole_0)))
% 0.37/0.57          | (v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0)
% 0.37/0.57          | ((X20) = (k1_xboole_0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.57  thf(t113_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i]:
% 0.37/0.57         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.57  thf(t4_subset_1, axiom,
% 0.37/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X20 : $i]:
% 0.37/0.57         ((v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0)
% 0.37/0.57          | ((X20) = (k1_xboole_0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['26', '28', '29'])).
% 0.37/0.57  thf('31', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['12', '20'])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i]:
% 0.37/0.57         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('33', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.37/0.57      inference('clc', [status(thm)], ['6', '22'])).
% 0.37/0.57  thf('34', plain, (((sk_B) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.57  thf('35', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.37/0.57      inference('demod', [status(thm)], ['31', '34'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.57  thf(cc1_subset_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.37/0.57          | (v1_xboole_0 @ X9)
% 0.37/0.57          | ~ (v1_xboole_0 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.37/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf('39', plain, (((sk_B) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.57  thf('41', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.57  thf('42', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.57  thf(t69_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.57       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      (![X3 : $i, X4 : $i]:
% 0.37/0.57         (~ (r1_xboole_0 @ X3 @ X4)
% 0.37/0.57          | ~ (r1_tarski @ X3 @ X4)
% 0.37/0.57          | (v1_xboole_0 @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.57  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.57      inference('sup-', [status(thm)], ['41', '44'])).
% 0.37/0.57  thf('46', plain, ((v1_xboole_0 @ sk_C)),
% 0.37/0.57      inference('demod', [status(thm)], ['38', '39', '40', '45'])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.57  thf('48', plain, (((sk_C) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.57  thf('49', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.37/0.57      inference('demod', [status(thm)], ['35', '48'])).
% 0.37/0.57  thf('50', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['30', '49'])).
% 0.37/0.57  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.57      inference('sup-', [status(thm)], ['41', '44'])).
% 0.37/0.57  thf('52', plain, ($false),
% 0.37/0.57      inference('demod', [status(thm)], ['24', '50', '51'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
