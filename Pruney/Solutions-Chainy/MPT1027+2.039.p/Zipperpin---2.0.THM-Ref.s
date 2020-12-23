%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XoDF7dOMiD

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 239 expanded)
%              Number of leaves         :   33 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  496 (2795 expanded)
%              Number of equality atoms :   42 ( 171 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['0','1','2'])).

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

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 )
      | ( zip_tseitin_1 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k1_relset_1 @ X11 @ X12 @ X13 ) )
      | ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ~ ( zip_tseitin_1 @ X13 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('14',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','15'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','14'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['20','21','23','24'])).

thf('26',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( v1_funct_2 @ X16 @ X15 @ X14 )
      | ( X16 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,(
    ! [X15: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X15 @ k1_xboole_0 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('31',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

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

thf('32',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[rc2_funct_2])).

thf('33',plain,(
    m1_subset_1 @ ( sk_B_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('35',plain,(
    m1_subset_1 @ ( sk_B_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X15: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X15 @ k1_xboole_0 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30','41'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','26'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','39'])).

thf('46',plain,(
    ! [X17: $i] :
      ( v1_funct_2 @ ( sk_B_1 @ X17 ) @ X17 @ X17 ) ),
    inference(cnf,[status(esa)],[rc2_funct_2])).

thf('47',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['27','44','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XoDF7dOMiD
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 88 iterations in 0.040s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.49  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(t130_funct_2, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.20/0.49         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.20/0.49            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.49        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 0.20/0.49        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.20/0.49  thf(d1_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.49           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.49             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.49           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.49             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_1, axiom,
% 0.20/0.49    (![B:$i,A:$i]:
% 0.20/0.49     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.49       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         ((zip_tseitin_0 @ X9 @ X10) | ((X9) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_3, axiom,
% 0.20/0.49    (![C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.49       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_5, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.49           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (zip_tseitin_0 @ X14 @ X15)
% 0.20/0.49          | (zip_tseitin_1 @ X16 @ X14 @ X15)
% 0.20/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A)
% 0.20/0.49        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((((sk_B_2) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.49  thf('9', plain, (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C) = (sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (((X11) != (k1_relset_1 @ X11 @ X12 @ X13))
% 0.20/0.49          | (v1_funct_2 @ X13 @ X11 @ X12)
% 0.20/0.49          | ~ (zip_tseitin_1 @ X13 @ X12 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((sk_A) != (sk_A))
% 0.20/0.49        | ~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A)
% 0.20/0.49        | (v1_funct_2 @ sk_C @ sk_A @ sk_B_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 0.20/0.49        | ~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.49  thf('13', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.20/0.49  thf('14', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '14'])).
% 0.20/0.49  thf('16', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '15'])).
% 0.20/0.49  thf(t9_mcart_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.49                 ( ![C:$i,D:$i]:
% 0.20/0.49                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.49                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t5_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.49          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.49          | ~ (v1_xboole_0 @ X5)
% 0.20/0.49          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '14'])).
% 0.20/0.49  thf(t113_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '23', '24'])).
% 0.20/0.49  thf('26', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '25'])).
% 0.20/0.49  thf('27', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.49         (((X14) != (k1_xboole_0))
% 0.20/0.49          | ((X15) = (k1_xboole_0))
% 0.20/0.49          | (v1_funct_2 @ X16 @ X15 @ X14)
% 0.20/0.49          | ((X16) != (k1_xboole_0))
% 0.20/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X15 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ k1_xboole_0)))
% 0.20/0.49          | (v1_funct_2 @ k1_xboole_0 @ X15 @ k1_xboole_0)
% 0.20/0.49          | ((X15) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf(rc2_funct_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ?[B:$i]:
% 0.20/0.49       ( ( v3_funct_2 @ B @ A @ A ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.49         ( v1_funct_1 @ B ) & ( v5_relat_1 @ B @ A ) & 
% 0.20/0.49         ( v4_relat_1 @ B @ A ) & ( v1_relat_1 @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X17 : $i]:
% 0.20/0.49         (m1_subset_1 @ (sk_B_1 @ X17) @ 
% 0.20/0.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.20/0.49      inference('cnf', [status(esa)], [rc2_funct_2])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((m1_subset_1 @ (sk_B_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((m1_subset_1 @ (sk_B_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.49          | ~ (v1_xboole_0 @ X5)
% 0.20/0.49          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (sk_B_1 @ k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('39', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '39'])).
% 0.20/0.49  thf('41', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X15 : $i]:
% 0.20/0.49         ((v1_funct_2 @ k1_xboole_0 @ X15 @ k1_xboole_0)
% 0.20/0.49          | ((X15) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30', '41'])).
% 0.20/0.49  thf('43', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '26'])).
% 0.20/0.49  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '39'])).
% 0.20/0.49  thf('46', plain, (![X17 : $i]: (v1_funct_2 @ (sk_B_1 @ X17) @ X17 @ X17)),
% 0.20/0.49      inference('cnf', [status(esa)], [rc2_funct_2])).
% 0.20/0.49  thf('47', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain, ($false),
% 0.20/0.49      inference('demod', [status(thm)], ['27', '44', '47'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
