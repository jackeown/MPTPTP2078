%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hArgI6rmMH

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 195 expanded)
%              Number of leaves         :   33 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  524 (2318 expanded)
%              Number of equality atoms :   44 ( 136 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('2',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16
       != ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['6','10'])).

thf('12',plain,(
    ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('14',plain,(
    ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['2','11'])).

thf('15',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( v1_funct_2 @ X21 @ X20 @ X19 )
      | ( X21 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(rc2_funct_2,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v3_funct_2 @ B @ A @ A )
      & ( v1_funct_2 @ B @ A @ A )
      & ( v1_funct_1 @ B )
      & ( v5_relat_1 @ B @ A )
      & ( v4_relat_1 @ B @ A )
      & ( v1_relat_1 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) )).

thf('23',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[rc2_funct_2])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[rc2_funct_2])).

thf('31',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X20: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','20','34'])).

thf('36',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('37',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('38',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('44',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','47'])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('51',plain,(
    ! [X14: $i] :
      ( zip_tseitin_0 @ X14 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['16','49','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hArgI6rmMH
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:23:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 107 iterations in 0.047s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(t130_funct_2, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.21/0.52         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.21/0.52            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d1_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_2, axiom,
% 0.21/0.52    (![C:$i,B:$i,A:$i]:
% 0.21/0.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_4, axiom,
% 0.21/0.52    (![B:$i,A:$i]:
% 0.21/0.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.52       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.52  thf(zf_stmt_5, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.21/0.52          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.21/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (((zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A)
% 0.21/0.52        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('3', plain, (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C) = (sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.52         (((X16) != (k1_relset_1 @ X16 @ X17 @ X18))
% 0.21/0.52          | (v1_funct_2 @ X18 @ X16 @ X17)
% 0.21/0.52          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((((sk_A) != (sk_A))
% 0.21/0.52        | ~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A)
% 0.21/0.52        | (v1_funct_2 @ sk_C @ sk_A @ sk_B_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 0.21/0.52        | ~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A))),
% 0.21/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 0.21/0.52        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.52  thf('11', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['6', '10'])).
% 0.21/0.52  thf('12', plain, (~ (zip_tseitin_0 @ sk_B_2 @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['2', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.52  thf('14', plain, (~ (zip_tseitin_0 @ sk_B_2 @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['2', '11'])).
% 0.21/0.52  thf('15', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.52         (((X19) != (k1_xboole_0))
% 0.21/0.52          | ((X20) = (k1_xboole_0))
% 0.21/0.52          | (v1_funct_2 @ X21 @ X20 @ X19)
% 0.21/0.52          | ((X21) != (k1_xboole_0))
% 0.21/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X20 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ k1_xboole_0)))
% 0.21/0.52          | (v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0)
% 0.21/0.52          | ((X20) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.52  thf(t113_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.52  thf(t6_mcart_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.52                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.21/0.52                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.21/0.52                       ( r2_hidden @ G @ B ) ) =>
% 0.21/0.52                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.52  thf(rc2_funct_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ?[B:$i]:
% 0.21/0.52       ( ( v3_funct_2 @ B @ A @ A ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.52         ( v1_funct_1 @ B ) & ( v5_relat_1 @ B @ A ) & 
% 0.21/0.52         ( v4_relat_1 @ B @ A ) & ( v1_relat_1 @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X22 : $i]:
% 0.21/0.52         (m1_subset_1 @ (sk_B_1 @ X22) @ 
% 0.21/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.21/0.52      inference('cnf', [status(esa)], [rc2_funct_2])).
% 0.21/0.52  thf(t5_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.52          | ~ (v1_xboole_0 @ X7)
% 0.21/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.21/0.52          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (sk_B_1 @ k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.52  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X22 : $i]:
% 0.21/0.52         (m1_subset_1 @ (sk_B_1 @ X22) @ 
% 0.21/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.21/0.52      inference('cnf', [status(esa)], [rc2_funct_2])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.52  thf('34', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['31', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X20 : $i]:
% 0.21/0.52         ((v1_funct_2 @ k1_xboole_0 @ X20 @ k1_xboole_0)
% 0.21/0.52          | ((X20) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['18', '20', '34'])).
% 0.21/0.52  thf('36', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.52  thf('37', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('38', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.52          | ~ (v1_xboole_0 @ X7)
% 0.21/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.52  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.21/0.52  thf('47', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '46'])).
% 0.21/0.52  thf('48', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['38', '47'])).
% 0.21/0.52  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ X14 @ X15) | ((X15) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.52  thf('51', plain, (![X14 : $i]: (zip_tseitin_0 @ X14 @ k1_xboole_0)),
% 0.21/0.52      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.52  thf('52', plain, ($false),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '49', '51'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
