%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Selbr3pWaO

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:00 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 127 expanded)
%              Number of leaves         :   36 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  489 (1295 expanded)
%              Number of equality atoms :   24 (  66 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v5_relat_1 @ sk_D @ sk_B_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X18 @ X17 ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v5_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['25','37'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ sk_D ),
    inference(demod,[status(thm)],['22','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['19','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Selbr3pWaO
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 123 iterations in 0.123s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.59  thf(t7_funct_2, conjecture,
% 0.41/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.59       ( ( r2_hidden @ C @ A ) =>
% 0.41/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.41/0.59           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.59            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.59          ( ( r2_hidden @ C @ A ) =>
% 0.41/0.59            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.41/0.59              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.41/0.59  thf('0', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(d1_funct_2, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_1, axiom,
% 0.41/0.59    (![C:$i,B:$i,A:$i]:
% 0.41/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.41/0.59         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.41/0.59          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.41/0.59          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.41/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.59  thf(zf_stmt_2, axiom,
% 0.41/0.59    (![B:$i,A:$i]:
% 0.41/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X29 : $i, X30 : $i]:
% 0.41/0.59         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.59  thf(zf_stmt_5, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.41/0.59         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.41/0.59          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.41/0.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.41/0.59        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['3', '6'])).
% 0.41/0.59  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('9', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.41/0.59         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.41/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.41/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.59  thf('13', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.41/0.59  thf(fc10_relat_1, axiom,
% 0.41/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X14 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ (k1_relat_1 @ X14)) | ~ (v1_xboole_0 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.41/0.59  thf('15', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 0.41/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('16', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(d1_xboole_0, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.59  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.41/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('19', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.41/0.59      inference('clc', [status(thm)], ['15', '18'])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc4_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.41/0.59       ( ![C:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.41/0.59           ( v1_xboole_0 @ C ) ) ) ))).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ X23)
% 0.41/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.41/0.59          | (v1_xboole_0 @ X24))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.41/0.59  thf('22', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc2_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.59         ((v5_relat_1 @ X20 @ X22)
% 0.41/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.59  thf('25', plain, ((v5_relat_1 @ sk_D @ sk_B_1)),
% 0.41/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.59  thf('26', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('27', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.41/0.59  thf(t176_funct_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.59       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.41/0.59         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.41/0.59          | (m1_subset_1 @ (k1_funct_1 @ X18 @ X17) @ X19)
% 0.41/0.59          | ~ (v1_funct_1 @ X18)
% 0.41/0.59          | ~ (v5_relat_1 @ X18 @ X19)
% 0.41/0.59          | ~ (v1_relat_1 @ X18))),
% 0.41/0.59      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.59          | ~ (v1_relat_1 @ sk_D)
% 0.41/0.59          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.41/0.59          | ~ (v1_funct_1 @ sk_D)
% 0.41/0.59          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc2_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.41/0.59          | (v1_relat_1 @ X10)
% 0.41/0.59          | ~ (v1_relat_1 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.59  thf('32', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.41/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf(fc6_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.59  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.59          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.41/0.59          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.41/0.59      inference('demod', [status(thm)], ['29', '34', '35'])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ X0)
% 0.41/0.59          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['26', '36'])).
% 0.41/0.59  thf('38', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.41/0.59      inference('sup-', [status(thm)], ['25', '37'])).
% 0.41/0.59  thf(t2_subset, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ A @ B ) =>
% 0.41/0.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (![X5 : $i, X6 : $i]:
% 0.41/0.59         ((r2_hidden @ X5 @ X6)
% 0.41/0.59          | (v1_xboole_0 @ X6)
% 0.41/0.59          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [t2_subset])).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.59        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.59  thf('41', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('42', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.41/0.59      inference('clc', [status(thm)], ['40', '41'])).
% 0.41/0.59  thf('43', plain, ((v1_xboole_0 @ sk_D)),
% 0.41/0.59      inference('demod', [status(thm)], ['22', '42'])).
% 0.41/0.59  thf('44', plain, ($false), inference('demod', [status(thm)], ['19', '43'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
