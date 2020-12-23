%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IfBUvhnZru

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:57 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 154 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  526 (1677 expanded)
%              Number of equality atoms :   26 (  80 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X10 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('22',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('27',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['34','37'])).

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
    v1_xboole_0 @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['33','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['24','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IfBUvhnZru
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:18:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.35/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.57  % Solved by: fo/fo7.sh
% 0.35/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.57  % done 84 iterations in 0.073s
% 0.35/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.57  % SZS output start Refutation
% 0.35/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.57  thf(t7_funct_2, conjecture,
% 0.35/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.57       ( ( r2_hidden @ C @ A ) =>
% 0.35/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.57           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.57          ( ( r2_hidden @ C @ A ) =>
% 0.35/0.57            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.57              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.35/0.57    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.35/0.57  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(d1_funct_2, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_1, axiom,
% 0.35/0.57    (![C:$i,B:$i,A:$i]:
% 0.35/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.57  thf('2', plain,
% 0.35/0.57      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.57         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.35/0.57          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.35/0.57          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('3', plain,
% 0.35/0.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.35/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.57  thf(zf_stmt_2, axiom,
% 0.35/0.57    (![B:$i,A:$i]:
% 0.35/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.35/0.57  thf('4', plain,
% 0.35/0.57      (![X24 : $i, X25 : $i]:
% 0.35/0.57         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.57  thf('5', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.57  thf(zf_stmt_5, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.57  thf('6', plain,
% 0.35/0.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.35/0.57         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.35/0.57          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.35/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.57  thf('7', plain,
% 0.35/0.57      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.35/0.57        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.57  thf('8', plain,
% 0.35/0.57      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['4', '7'])).
% 0.35/0.57  thf('9', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.35/0.57  thf('11', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.57  thf('12', plain,
% 0.35/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.57         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.35/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.57  thf('13', plain,
% 0.35/0.57      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.35/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.57  thf('14', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.35/0.57      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.35/0.57  thf(t12_funct_1, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.57         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.35/0.57  thf('15', plain,
% 0.35/0.57      (![X10 : $i, X11 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.35/0.57          | (r2_hidden @ (k1_funct_1 @ X11 @ X10) @ (k2_relat_1 @ X11))
% 0.35/0.57          | ~ (v1_funct_1 @ X11)
% 0.35/0.57          | ~ (v1_relat_1 @ X11))),
% 0.35/0.57      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.35/0.57  thf('16', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.57          | ~ (v1_relat_1 @ sk_D)
% 0.35/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.35/0.57          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.57  thf('17', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(cc1_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( v1_relat_1 @ C ) ))).
% 0.35/0.57  thf('18', plain,
% 0.35/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.57         ((v1_relat_1 @ X12)
% 0.35/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.35/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.57  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.57  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('21', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.57          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.35/0.57      inference('demod', [status(thm)], ['16', '19', '20'])).
% 0.35/0.57  thf('22', plain,
% 0.35/0.57      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.35/0.57      inference('sup-', [status(thm)], ['0', '21'])).
% 0.35/0.57  thf(d1_xboole_0, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.57  thf('23', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.35/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.35/0.57  thf('24', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_D))),
% 0.35/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.57  thf('25', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(dt_k2_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.35/0.57  thf('26', plain,
% 0.35/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.57         ((m1_subset_1 @ (k2_relset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.35/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.35/0.57  thf('27', plain,
% 0.35/0.57      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ 
% 0.35/0.57        (k1_zfmisc_1 @ sk_B_1))),
% 0.35/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.57  thf('28', plain,
% 0.35/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.57  thf('29', plain,
% 0.35/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.57         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.35/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.57  thf('30', plain,
% 0.35/0.57      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.35/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.57  thf('31', plain,
% 0.35/0.57      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.35/0.57      inference('demod', [status(thm)], ['27', '30'])).
% 0.35/0.57  thf(cc1_subset_1, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.35/0.57  thf('32', plain,
% 0.35/0.57      (![X3 : $i, X4 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.35/0.57          | (v1_xboole_0 @ X3)
% 0.35/0.57          | ~ (v1_xboole_0 @ X4))),
% 0.35/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.35/0.57  thf('33', plain,
% 0.35/0.57      ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_relat_1 @ sk_D)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.57  thf('34', plain,
% 0.35/0.57      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.35/0.57      inference('sup-', [status(thm)], ['0', '21'])).
% 0.35/0.57  thf('35', plain,
% 0.35/0.57      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.35/0.57      inference('demod', [status(thm)], ['27', '30'])).
% 0.35/0.57  thf(t4_subset, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.35/0.57       ( m1_subset_1 @ A @ C ) ))).
% 0.35/0.57  thf('36', plain,
% 0.35/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X7 @ X8)
% 0.35/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.35/0.57          | (m1_subset_1 @ X7 @ X9))),
% 0.35/0.57      inference('cnf', [status(esa)], [t4_subset])).
% 0.35/0.57  thf('37', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.35/0.57          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.57  thf('38', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.35/0.57      inference('sup-', [status(thm)], ['34', '37'])).
% 0.35/0.57  thf(t2_subset, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.57  thf('39', plain,
% 0.35/0.57      (![X5 : $i, X6 : $i]:
% 0.35/0.57         ((r2_hidden @ X5 @ X6)
% 0.35/0.57          | (v1_xboole_0 @ X6)
% 0.35/0.57          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.35/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.57  thf('40', plain,
% 0.35/0.57      (((v1_xboole_0 @ sk_B_1)
% 0.35/0.57        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1))),
% 0.35/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.35/0.57  thf('41', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('42', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.35/0.57      inference('clc', [status(thm)], ['40', '41'])).
% 0.35/0.57  thf('43', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_D))),
% 0.35/0.57      inference('demod', [status(thm)], ['33', '42'])).
% 0.35/0.57  thf('44', plain, ($false), inference('demod', [status(thm)], ['24', '43'])).
% 0.35/0.57  
% 0.35/0.57  % SZS output end Refutation
% 0.35/0.57  
% 0.35/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
