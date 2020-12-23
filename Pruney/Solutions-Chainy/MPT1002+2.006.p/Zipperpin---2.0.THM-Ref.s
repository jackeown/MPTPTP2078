%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AqYnzaLDcj

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 134 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  610 (1715 expanded)
%              Number of equality atoms :   56 ( 137 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t50_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k7_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k9_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k8_relset_1 @ X18 @ X19 @ X17 @ X20 )
        = ( k10_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('20',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('25',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['23','30','31','32'])).

thf('34',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('35',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','35'])).

thf('37',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['16','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','37','40'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( r1_tarski @ X8 @ ( k10_relat_1 @ X9 @ ( k9_relat_1 @ X9 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['4','7','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AqYnzaLDcj
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 114 iterations in 0.111s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(t50_funct_2, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( ( r1_tarski @ C @ A ) =>
% 0.21/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.56           ( r1_tarski @
% 0.21/0.56             C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.56            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56          ( ( r1_tarski @ C @ A ) =>
% 0.21/0.56            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.56              ( r1_tarski @
% 0.21/0.56                C @ 
% 0.21/0.56                ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t50_funct_2])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (~ (r1_tarski @ sk_C @ 
% 0.21/0.56          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ 
% 0.21/0.56           (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.21/0.56          | ((k7_relset_1 @ X14 @ X15 @ X13 @ X16) = (k9_relat_1 @ X13 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (~ (r1_tarski @ sk_C @ 
% 0.21/0.56          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.21/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.56          | ((k8_relset_1 @ X18 @ X19 @ X17 @ X20) = (k10_relat_1 @ X17 @ X20)))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf('8', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d1_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_1, axiom,
% 0.21/0.56    (![C:$i,B:$i,A:$i]:
% 0.21/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.56         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.21/0.56          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.21/0.56          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.21/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.56  thf(zf_stmt_2, axiom,
% 0.21/0.56    (![B:$i,A:$i]:
% 0.21/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X21 : $i, X22 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_5, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.56         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.21/0.56          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.21/0.56          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.56  thf('17', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['17'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (~ (r1_tarski @ sk_C @ 
% 0.21/0.56          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ 
% 0.21/0.56           (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_C @ 
% 0.21/0.56           (k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ 
% 0.21/0.56            (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C))))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['17'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_C @ 
% 0.21/0.56           (k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ 
% 0.21/0.56            (k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C))))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['17'])).
% 0.21/0.56  thf('25', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf(d10_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X2 : $i]:
% 0.21/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.56  thf('29', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.56  thf('32', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf('33', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['23', '30', '31', '32'])).
% 0.21/0.56  thf('34', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.21/0.56      inference('split', [status(esa)], ['17'])).
% 0.21/0.56  thf('35', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['18', '35'])).
% 0.21/0.56  thf('37', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['16', '36'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.21/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['11', '37', '40'])).
% 0.21/0.56  thf(t146_funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.56         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 0.21/0.57          | (r1_tarski @ X8 @ (k10_relat_1 @ X9 @ (k9_relat_1 @ X9 @ X8)))
% 0.21/0.57          | ~ (v1_relat_1 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X0 @ sk_A)
% 0.21/0.57          | ~ (v1_relat_1 @ sk_D)
% 0.21/0.57          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc2_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.57          | (v1_relat_1 @ X4)
% 0.21/0.57          | ~ (v1_relat_1 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf(fc6_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.57  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X0 @ sk_A)
% 0.21/0.57          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0))))),
% 0.21/0.57      inference('demod', [status(thm)], ['43', '48'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '49'])).
% 0.21/0.57  thf('51', plain, ($false),
% 0.21/0.57      inference('demod', [status(thm)], ['4', '7', '50'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
